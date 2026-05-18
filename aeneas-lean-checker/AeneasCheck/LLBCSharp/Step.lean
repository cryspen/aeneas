import AeneasCheck.LLBCSharp.State

/-!
Per-event step relation for LLBC#.

Each function corresponds to one rule in Fig. 4 of the 2022 paper (and
later figures). For M6 we implement:
* E-MutBorrow (also covers in-body fresh borrows),
* E-Move / E-Copy / E-Assign (operands feeding an assign),
* Reorg-End-MutBorrow (`endBorrow`),
* E-Return / E-Panic / E-Assert.

Each `step*` function returns `.ok newState` or `.error msg`. Failures
correspond to cert violations the LLBC# semantics would not derive.
-/

namespace AeneasCheck.LLBCSharp

open AeneasCheck.Raw

abbrev Result α := Except String α

private def fail {α} (msg : String) : Result α := .error msg

/-- Resolve a place's "root local" — the local whose value the place
    ultimately reads or writes. Projection chains are tracked but the
    M6 replayer does not yet model nested data; field/deref projections
    reduce to the root local. M9+ refines this for nested borrows. -/
def placeRootLocal (p : Place) : Nat := p.local_

/-- Resolve a `SymExpr` in the current state. -/
def evalSymExpr (st : SymState) (e : SymExpr) : Result Val := do
  match e with
  | .symVal id => return .sym id
  | .symLit l => return .lit l
  | .symCopy p =>
    let v := st.getLocal (placeRootLocal p)
    return v
  | .symMove p =>
    let v := st.getLocal (placeRootLocal p)
    return v
  | .symMutBorrowTok b => return .mutLoan b
  | .symVariant _ vid _ _ =>
    -- M9.5d / M9.5f: an enum variant ctor. The abstract symbolic state
    -- doesn't (yet) model ADT values structurally; we project the
    -- variant id onto a fresh symbolic value tag so the replayer can
    -- thread it through subsequent reads. This is sound for M9.5d's
    -- forward-only checking — the Lean translator handles the actual
    -- match-arm semantics through the EvMatchArm event log. M9.5f's
    -- payload fields don't affect the abstract state at this layer.
    return .sym vid
  | .symTuple _ =>
    -- M9.5p: tuple aggregate. Same treatment as `symVariant` — the
    -- abstract state doesn't model tuple values structurally; the
    -- Lean translator handles the rendering. Project to a fresh
    -- sym-0 token; the trace's subsequent reads only need the
    -- assignment to have *some* witness, which the EvAssign produces.
    return .sym 0
  | .symRecord _ _ =>
    -- M9.5p: named-field struct aggregate. Same rationale as
    -- `symTuple`: the abstract state is field-less; the Lean
    -- translator handles record-literal rendering via the EvAssign
    -- rhs. Project to a fresh sym-0 token.
    return .sym 0

/-! ## E-MutBorrow

The OCaml interpreter emits this event when a `&mut p` rvalue is
evaluated. The place's current value moves into the new mut-borrow
body; the place is replaced by a `mutLoan b` token tracking the loan.
-/

def stepMutBorrow (st : SymState) (loan : Nat) (place : Place)
    (_symval : Nat) (kindHint : MutBorrowKind := .direct) :
    Result SymState := do
  if st.loans.contains loan then
    fail s!"E-MutBorrow: borrow id {loan} already live"
  else if st.loanIdHwm > loan then
    -- M10.x.2: monotone-allocator strengthening. The OCaml interpreter's
    -- loan-id counter is monotone; a fresh-loan event with id below the
    -- current HWM is a cert violation (re-use of a previously-issued id).
    -- Soundness consumer: CertGen_faithful.mutBorrow_{direct,inAbsReborrow,
    -- loopOwned}'s `st.loanIdHwm ≤ loan` clause becomes a direct `hStep`
    -- inversion. G4 sweep: zero pre-flight violations.
    fail s!"E-MutBorrow: borrow id {loan} below HWM {st.loanIdHwm}"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-MutBorrow: local {root} out of bounds (have {st.numLocals})"
    else
      -- M9.6 (Option C, plan §7.1 #23) — strict-only path: trust
      -- the OCaml-supplied [kindHint] verbatim. The M9.5w
      -- Deref-projection fallback is retired here — the OCaml
      -- emitter (commit #4) sets MbkInAbsReborrow for any
      -- &mut (*x).f shape that isn't already an EvReborrow, so a
      -- .direct hint on a place with a Deref projection is now a
      -- cert bug rather than something to recover from. (For
      -- legacy v1 / hint-empty certs this means the .direct case
      -- treats Deref-bearing places as truly direct, which the
      -- exit `leakedDirect` check then catches.)
      match kindHint with
      | .inAbsReborrow _ =>
        return st.addLoan loan .bottom .reborrow
      | .loopOwned _ =>
        let inner := st.getLocal root
        let st := st.setLocal root (.mutLoan loan)
        return st.addLoan loan inner .lazyExpand
      | .direct =>
        let inner := st.getLocal root
        let st := st.setLocal root (.mutLoan loan)
        return st.addLoan loan inner .direct

/-! ## E-SharedBorrow

Creating a shared borrow does not move the place's value out — both
the original local and the borrower can read it concurrently. The
M9.2 structural check only verifies the borrow id is fresh and the
place is in range; full LLBC# shared-loan algebra lands in M11. -/

def stepSharedBorrow (st : SymState) (loan : Nat) (_sbId : Nat)
    (place : Place) (_symval : Nat) : Result SymState := do
  if st.loans.contains loan then
    fail s!"E-SharedBorrow: borrow id {loan} already live"
  else if st.loanIdHwm > loan then
    -- M10.x.2: monotone-allocator strengthening, mirrors stepMutBorrow.
    -- Discharges CertGen_faithful.sharedBorrow's `st.loanIdHwm ≤ loan`
    -- clause via hStep inversion. G4 sweep: zero pre-flight violations
    -- (no fixture currently emits EvSharedBorrow, but the check is in
    -- place for future v6+ fixtures).
    fail s!"E-SharedBorrow: borrow id {loan} below HWM {st.loanIdHwm}"
  else if place.projection.size ≠ 0 then
    -- M10.x.2: projection-empty strengthening. The replayer operates on
    -- `placeRootLocal` and ignores the projection chain; the paper-side
    -- `LStep.sharedBorrow` resolves the full place. Cert-emission
    -- discipline mandates a root-only place here; future M10.x.3+
    -- adjustments to the axiom may revisit. G4 sweep: zero violations
    -- (no fixture emits EvSharedBorrow).
    fail s!"E-SharedBorrow: place.projection non-empty (size {place.projection.size}) — projection chain not supported"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-SharedBorrow: local {root} out of bounds (have {st.numLocals})"
    else
      let inner := st.getLocal root
      return st.addLoan loan inner .shared

/-! ## E-Reborrow

The OCaml interpreter emits this event when a `&mut p` rvalue is
evaluated and the place [p] dereferences an existing parent borrow
(i.e. [p.projection] ends with [Deref] of a [VBorrow] value). The
parent's loan must still be live; the child's id must be fresh. -/

def stepReborrow (st : SymState) (child parent : Nat) (place : Place)
    (parentLive : Bool := false) (_parentAbs : Option Nat := none) :
    Result SymState := do
  if st.loans.contains child then
    fail s!"E-Reborrow: child borrow id {child} already live"
  else if st.loanIdHwm > child then
    -- M10.x.2: monotone-allocator strengthening on the child id.
    -- Discharges CertGen_faithful.reborrow's `st.loanIdHwm ≤ child`
    -- clause via hStep inversion. G4 sweep: zero pre-flight violations
    -- for the child side. The parent-side `parent < st.loanIdHwm`
    -- strengthening (audit row 2) was infeasible (95 pre-flight
    -- violations from abs-internal parent loans the Lean SymState
    -- never tracked allocation for); the existing pre-add fallback at
    -- the bottom of this function continues to handle that case until
    -- M10.x.4 (or a later commit) registers parent abs upstream.
    fail s!"E-Reborrow: child borrow id {child} below HWM {st.loanIdHwm}"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-Reborrow: local {root} out of bounds (have {st.numLocals})"
    else
      -- M9.6 (Option C, plan §4.1.4) — strict path: when the OCaml
      -- side declares [parentLive = true] AND the parent loan IS
      -- in our state, accept; when [parentLive = true] but the
      -- parent isn't tracked (the OCaml loan lookup found it
      -- inside an abstraction the Lean SymState doesn't model),
      -- fall back to the pre-add-as-`.reborrow` behaviour rather
      -- than erroring — same tolerance pattern as
      -- [stepSymExpandMutBorrow.subst_locals]. When
      -- [parentLive = false] (also the back-compat default for
      -- v1 / hint-empty certs), behaviour is the same. The
      -- [parentAbs] hint is recorded by commit #19's
      -- AbsRegistry consumer; ignored here.
      let st :=
        if st.loans.contains parent then st
        else st.addLoan parent .bottom .reborrow
      -- The new child borrow's body is the inner value of the parent
      -- chain. The M9.2 structural check uses `.bottom` as a
      -- sentinel since we don't model nested-borrow values yet; the
      -- restoration on EvEndBorrow uses the cert's [given_back]
      -- which carries the real symbolic value. The `.reborrow` kind
      -- tells `stepEndBorrow` not to scan env for a `mutLoan` token.
      return st.addLoan child .bottom .reborrow

/-! ## Reorg-End-MutBorrow

End an active mut borrow: the [given_back] value from the cert flows
back to the loan slot. We additionally check that the loan side of the
state really holds a `mutLoan loan` token — this is the LLBC#
precondition that rules out double-frees.
-/

def stepEndBorrow (st : SymState) (loan : Nat) (restore : RestoreInfo)
    : Result SymState := do
  match st.takeLoan loan with
  | none =>
    -- M9.6: the OCaml cert emitter (commit #12) no longer emits
    -- the redundant post-join EvEndBorrow that the M9.5x silent
    -- re-end branch used to tolerate. A miss here is now a hard
    -- cert violation.
    fail s!"end-borrow: borrow id {loan} not live"
  | some (li, st) => do
    let v ← evalSymExpr st restore.givenBack
    match li.kind with
    | .direct | .lazyExpand => do
      -- `.direct`: created via E-MutBorrow — the place was replaced
      -- with a `mutLoan` token; end-borrow restores from `given_back`.
      -- `.lazyExpand` (M9.5r): created via E-SymExpandMutBorrow on a
      -- function-call return; same end-borrow semantics, but its
      -- lifetime is owned by an abstraction (so it's allowed to
      -- "leak" past function exit per the post-condition in
      -- Replay.lean).
      --
      -- M10.x.9: cert v6 `restore.holderLocal` hint drives a
      -- single-shot env update; falls back to `findHolder` (a pure
      -- env-walk helper) when the cert omits the hint (legacy
      -- emit-sites or `holderLocal = none`). For `.lazyExpand`, a
      -- missing or mismatched holder triggers the leak path (return
      -- `st` unchanged); for `.direct`, it's a hard fail. The
      -- soundness proof inverts this dispatch directly, replacing
      -- the previous `CertGen_faithful.endBorrow_direct_witness`
      -- axiom.
      let holderOpt := restore.holderLocal.orElse (fun () => findHolder st loan)
      match holderOpt with
      | some x =>
        match st.env[x]? with
        | some (.mutLoan b) =>
          if b = loan then
            return { st with env := st.env.insert x v }
          else if li.kind == .lazyExpand then return st
          else fail s!"end-borrow: local {x} holds mutLoan {b} ≠ {loan}"
        | _ =>
          if li.kind == .lazyExpand then return st
          else fail s!"end-borrow: local {x} doesn't hold mutLoan {loan}"
      | none =>
        if li.kind == .lazyExpand then return st
        else fail s!"end-borrow: no local holds loan {loan}"
    | .reborrow =>
      -- A reborrow doesn't park a `mutLoan` token in env (the parent's
      -- token is still there); ending it only releases the loan id.
      return st
    | .shared =>
      -- Shared borrows don't replace the local value either; ending
      -- just drops the loan id.
      return st

/-! ## E-Move / E-Copy / E-Assign / E-Assert / E-Panic / E-Return -/

def stepMove (st : SymState) (src dst : Place) : Result SymState := do
  let v := st.getLocal (placeRootLocal src)
  let st := st.setLocal (placeRootLocal src) .bottom
  let st := st.setLocal (placeRootLocal dst) v
  return st

def stepCopy (st : SymState) (src dst : Place) : Result SymState := do
  let v := st.getLocal (placeRootLocal src)
  let st := st.setLocal (placeRootLocal dst) v
  return st

def stepAssign (st : SymState) (dst : Place) (rhs : SymExpr) :
    Result SymState := do
  let v ← evalSymExpr st rhs
  return st.setLocal (placeRootLocal dst) v

/-! ## E-BinaryOp

M10.0 structural rule: evaluate operands in the current state, bind
the destination local to a sentinel `bottom` (the symbolic-binop
result; the Pure translator carries the operand expressions
directly). The `op` tag is not interpreted here — the translator
maps it to a Lean operator. -/

def stepBinop (st : SymState) (_op : String) (lhs rhs : SymExpr)
    (dst : Place) : Result SymState := do
  let _ ← evalSymExpr st lhs
  let _ ← evalSymExpr st rhs
  let root := placeRootLocal dst
  if root ≥ st.numLocals then
    fail s!"E-BinaryOp: local {root} out of bounds (have {st.numLocals})"
  else
    return st.setLocal root (.sym 0)

/-! ## E-Call (forward only)

M10.1 structural rule: bind the destination local to a fresh
symbolic placeholder. Backward functions / region abstractions are
M10.2 work — for forward-only `wrapping_add`-style calls the dst
binding is all the replayer needs to thread the trace through. -/

def stepCall (st : SymState) (dst : Place) (absSig : Array AbsShape := #[]) :
    Result SymState := do
  let root := placeRootLocal dst
  if root ≥ st.numLocals then
    fail s!"E-Call: dst local {root} out of bounds (have {st.numLocals})"
  else
    -- M9.6 (Option C, plan §4.1.8): record each new abstraction's
    -- shape in [absRegistry] so [stepEndAbs] can later validate
    -- that the abstraction releases exactly the loans (and clears
    -- the locals) it owns. Empty [absSig] (v1 / hint-empty
    -- default) is a no-op. M10.1i: each insert also bumps the
    -- soundness-mirror `absIdHwm` past `shape.absId`.
    let st := absSig.foldl (init := st) SymState.addAbsShape
    return (st.setLocal root (.sym 0))

/-! ## E-SymExpandMutBorrow

M9.5r structural rule: the OCaml interpreter just expanded a symbolic
[&mut T] value (typically a function-call return) into a concrete
mut-borrow. We mirror the substitution in [SymState]: every local
holding [.sym svId] becomes [.mutLoan bid], and we register loan
[bid] with [given := .sym innerSv] so the inner value can flow back
on a subsequent [EvEndBorrow loan=bid].

We also walk loan-given values for the same substitution: if any
existing loan was given a [.sym svId] (i.e. its restoration value was
a not-yet-expanded borrow), it now carries [.mutLoan bid]. -/

def stepSymExpandMutBorrow (st : SymState) (svId bid innerSv : Nat)
    (_parentAbs : Option Nat := none)
    (substLocals : Array Nat := #[]) (substLoans : Array Nat := #[]) :
    Result SymState := do
  if st.loans.contains bid then
    fail s!"E-SymExpandMutBorrow: borrow id {bid} already live"
  else if st.loanIdHwm > bid then
    -- M10.x.8: monotone-allocator strengthening, mirrors stepMutBorrow.
    -- Discharges `CertGen_faithful.symExpandMutBorrow`'s `st.loanIdHwm ≤ bid`
    -- clause via hStep inversion. G4 pre-flight: no fixture currently
    -- violates this (all bid emissions are monotone-fresh).
    fail s!"E-SymExpandMutBorrow: borrow id {bid} below HWM {st.loanIdHwm}"
  else
    -- M9.6 (Option C, plan §7.1 #23) — strict-only path: the OCaml
    -- side enumerates the env locals and loan-given slots it
    -- touched (commit #6 source). The M9.5r scan-env fallback is
    -- gone. Unbound locals / unknown loans in the hints are tolerated
    -- silently (only tracked slots get rewritten). [parentAbs] is
    -- recorded by commit #19's AbsRegistry consumer; ignored here.
    --
    -- M10.x.8: refactored from `for + mut` to explicit `Array.foldl`
    -- over `substLocalsOne` / `substLoansOne` so the soundness proof
    -- can chain per-step commute lemmas.
    let newEnv := substLocals.foldl (init := st.env) (substLocalsOne svId bid)
    let newLoans := substLoans.foldl (init := st.loans) (substLoansOne svId bid)
    let st := { st with env := newEnv, loans := newLoans }
    return st.addLoan bid (.sym innerSv) .lazyExpand

/-! ## E-EndAbstraction

M9.5s structural rule: a region abstraction just closed. Any loans
listed in `released` are loans the abstraction owned and whose
lifetime ends here — the OCaml interpreter's `end_abs_borrows`
implicitly drains them as it converts each [AMutBorrow] in the abs to
[AEndedMutBorrow] (and `give_back_value`s the symbolic into the
outer-context loan slot), without emitting an [EvEndBorrow] for each.

We mirror that here: drop each released loan from `st.loans`, and
clear any local that still holds the loan's `.mutLoan b` token (so the
post-check doesn't see a dead token). This is the missing piece that
makes the paper.rs `call_choose` pattern check — loan 1 flowed into
the call's abstraction, is implicitly ended on EvEndAbs, and so
must no longer count as "live at function exit". -/

/-- M10.x.6: pure post-validation body for `stepEndAbs`. Computes the
    deterministic post-state given that validation succeeded. Used by
    `stepEndAbs_sound` to side-step inversion on the validation `do`
    block; the soundness proof inverts `hStep` to extract this body's
    output and then applies the M10.x.6 commute lemmas. -/
def stepEndAbsBody (st : SymState) (absId : Nat) (released : Array Nat)
    (tokenClearLocals : Array Nat) : SymState :=
  let st := released.foldl (init := st) loansEraseIfPresent
  let newEnv := tokenClearLocals.foldl (init := st.env) tokenClearOne
  ({ st with env := newEnv } : SymState).removeAbsShape absId

/-- M10.x.6: validation half of `stepEndAbs`. Returns `()` on success,
    `fail` on a released loan not matching the abs's role list. Kept
    as a `Result Unit` so the do-block continues exactly when the
    cert's released list is consistent with the recorded abs shape. -/
def stepEndAbsValidate (st : SymState) (absId : Nat) (released : Array Nat) :
    Result Unit := do
  match st.absRegistry[absId]? with
  | none => pure ()
  | some shape =>
    let knownLoans : Std.HashSet Nat :=
      shape.roles.foldl (init := {}) fun s r =>
        match r with
        | .mutBorrow _ lid | .mutLoan lid => s.insert lid
        | .sharedBorrow _ _ => s
    for l in released do
      if !knownLoans.contains l then
        fail s!"E-EndAbs: abs {absId} released loan {l} not in its role list"

def stepEndAbs (st : SymState) (absId : Nat) (released : Array Nat)
    (tokenClearLocals : Array Nat := #[]) : Result SymState := do
  -- M9.6 (Option C, plan §4.1.8): validate released loans against the
  -- recorded abs role list (silent skip if absRegistry has no entry).
  -- M10.x.6 factored out as `stepEndAbsValidate` so the soundness
  -- proof can decouple validation-success from body-output.
  let _ ← stepEndAbsValidate st absId released
  -- M10.x.6: deterministic three-phase body (loan-erase fold →
  -- token-clear env fold → removeAbsShape). The fold structure
  -- mirrors the paper-side `LStep.endAbs` post-state's
  -- `tokenClearLocals.foldl clearMutLoanToken (Ω.removeAbs abs)`.
  return stepEndAbsBody st absId released tokenClearLocals

def stepAssert (_st : SymState) (cond : SymExpr) (expected : Bool) :
    Result Unit := do
  -- We don't model the assertion's truth value (symbolic execution
  -- can succeed even when the assertion is symbolic); the OCaml side
  -- having included this event means the rule fired. M11 strengthens
  -- this when joins land.
  match cond, expected with
  | .symLit (.bool b), e =>
    if b = e then return ()
    else fail s!"E-Assert: literal {b} disagrees with expected {e}"
  | _, _ => return ()

/-! ## E-Join (Fig. 11 of the 2024 long-version paper)

M11 structural rule: the OCaml interpreter witnessed a join after an
`if then else` (or `match`) and emitted three state summaries — the
two pre-join branches plus the joined post-state. The Lean replayer
re-checks the witness pragmatically and updates `SymState` to match
`result`.

The full LLBC# join algebra (six rules: Join-Same, Join-Symbolic,
Join-MutBorrows, Join-Var, Collapse-Merge-Abs, Collapse-Dup-MutBorrow)
is M12 work. For M11 we implement a pragmatic check that admits any
witness as long as each result entry is "≤-related" to both branches
in one of these ways:

  * **Join-Same**: `result.env[l]` is value-equal to *both*
    `left.env[l]` and `right.env[l]`. Encoded by `SymExpr.beq`.
  * **Join-Symbolic**: `result.env[l]` is a fresh `SymVal n` (i.e.,
    a symbolic-id form), and *either* the two branches disagree (so
    a fresh sym is the only way to subsume them) *or* one side is
    absent. We don't track which symbolic ids are "fresh" against
    the prior state — the cert promises that the result is sound,
    and M12 will tighten this.

What we *don't* check:
  * Shared-loan algebra, region abstraction merging
    (Collapse-Merge-Abs / Collapse-Dup-MutBorrow). The OCaml side
    has already run those reductions before emitting the witness.
  * The `≤` relation on borrow ids — we just take `result`'s
    `liveLoans` verbatim.
  * Entries present in a branch but absent from `result` — these
    correspond to locals that the join "dropped" (e.g. a dummy
    var); silently accepted.

After validation, `SymState` is updated: every local in
`result.env` is bound to the corresponding `Val`, and `loans` is
rebuilt with `liveLoans` (kind defaults to `.direct` — M12 fixes). -/

/-- Convert a cert `SymExpr` into a `Val`. Symbolic ids round-trip
    via `.sym`; literals via `.lit`; place reads / borrow tokens fall
    back to `.bottom` because the join witness doesn't carry place
    structure — the underlying OCaml ctx had already substituted
    them. -/
def valOfSymExpr : SymExpr → Val
  | .symVal n => .sym n
  | .symLit l => .lit l
  | .symCopy _ | .symMove _ => .bottom
  | .symMutBorrowTok b => .mutLoan b
  | .symVariant _ vid _ _ => .sym vid
  -- M9.5p: tuple / struct aggregate. The join witness doesn't carry
  -- aggregate-structure information; fall back to `.bottom` like the
  -- `symCopy`/`symMove` case.
  | .symTuple _ => .bottom
  | .symRecord _ _ => .bottom

/-- Structural equality on `SymExpr` cert values, used by the M9.6
    strict join check (and only there). Two `SymVal n` are equal
    iff `n` matches; two `SymLit` iff their underlying literals are
    `BEq`-equal; `SymMutBorrowTok` iff the borrow ids match;
    everything else conservatively "not equal". -/
def symExprBeq : SymExpr → SymExpr → Bool
  | .symVal a, .symVal b => a == b
  | .symLit (.bool a), .symLit (.bool b) => a == b
  | .symLit (.scalar ka a), .symLit (.scalar kb b) =>
    -- IntKind has no DecidableEq instance derived yet; compare via
    -- the string form which is stable per the M9 emitter.
    (Std.Format.pretty (repr ka)) == (Std.Format.pretty (repr kb)) && a == b
  | .symMutBorrowTok a, .symMutBorrowTok b => a == b
  | _, _ => false

/-- M9.6 (Option C, plan §4.1.2): strict per-entry validation
    driven by [EvJoin.witnesses]. Each [JoinEntry] names a
    Fig. 11 rule the OCaml interpreter applied; we re-check the
    side conditions:
      * JoinSame: left[l] == right[l] == result[l].
      * JoinSymbolic n: result[l] = SymVal n.
      * JoinMutBorrows l_l l_r l_f _: left = tok l_l, right =
        tok l_r, result = tok l_f.
      * JoinVar / JoinBottom* : marker only — accept (the
        soundness proof relies on the cert promise that these
        cases were derived from the paper rules).
    Returns the first failing entry's diagnostic, or [none] on
    success. -/
def joinEntryStrictOk (leftMap rightMap resultMap : Std.HashMap Nat SymExpr)
    (entry : JoinEntry) : Option String :=
  let l := entry.localId
  let r := resultMap[l]?
  match entry.rule, leftMap[l]?, rightMap[l]?, r with
  | .joinSame, some le, some re, some rE =>
    if symExprBeq le re && symExprBeq le rE then none
    else some s!"E-Join strict: JoinSame local {l} disagrees: left {repr le} right {repr re} result {repr rE}"
  | .joinSymbolic n, _, _, some rE =>
    (match rE with
     | .symVal m =>
       if n == m then none
       else some s!"E-Join strict: JoinSymbolic local {l} expected SymVal {n}, got SymVal {m}"
     | _ => some s!"E-Join strict: JoinSymbolic local {l} expected SymVal {n}, got {repr rE}")
  | .joinMutBorrows lL lR lF _, some le, some re, some rE =>
    let tokOk (e : SymExpr) (b : Nat) : Bool :=
      match e with
      | .symMutBorrowTok x => x == b
      | _ => false
    if tokOk le lL && tokOk re lR && tokOk rE lF then none
    else some s!"E-Join strict: JoinMutBorrows local {l} mismatch"
  | .joinVar, _, _, _ => none
  | .joinBottomOther _, _, _, _ => none
  | .joinOtherBottom _, _, _, _ => none
  | _, _, _, _ =>
    some s!"E-Join strict: rule {repr entry.rule} for local {l} missing required side"

/-- M10.x.10: one chain-fold step. Mirrors the paper-side
    `JoinEntryStep.<rule>` constructor on the SymState side. For
    rules whose paper-side constructor has a side condition (fresh
    loan id, fresh abs id, abs in registry) the replayer enforces
    the analogous SymState condition (HWM-fresh, registry-contains);
    failure fails the cert. The soundness side then extracts the
    paper-side premises from the `.ok` shape of this fold.

    Result-flavored (mirroring `Result` = `Except String`) so the
    `witnesses.foldlM` in `stepJoin` short-circuits on the first
    failure with a diagnostic. -/
def joinChainFoldStep (st : SymState) (entry : JoinEntry) :
    Result SymState := do
  match entry.rule with
  | .joinSame | .joinVar => return st
  | .joinSymbolic freshSv =>
    return st.setLocal entry.localId (.sym freshSv)
  | .joinMutBorrows _ _ l_fresh absShape =>
    if l_fresh < st.loanIdHwm then
      fail s!"E-Join chain: l_fresh {l_fresh} not HWM-fresh (HWM = {st.loanIdHwm})"
    else if absShape.absId < st.absIdHwm then
      fail s!"E-Join chain: abs.absId {absShape.absId} not HWM-fresh (HWM = {st.absIdHwm})"
    else
      return joinMutBorrowsStep st entry.localId l_fresh absShape
  | .joinBottomOther absId | .joinOtherBottom absId =>
    if !st.absRegistry.contains absId then
      fail s!"E-Join chain: abs {absId} not in registry"
    else
      return st

def stepJoin (st : SymState) (left right result : StateSummary)
    (witnesses : Array JoinEntry := #[])
    (strict : Bool := false) :
    Result SymState := do
  -- Build per-side hash maps from the env arrays for O(1) lookup.
  let leftMap : Std.HashMap Nat SymExpr :=
    left.env.foldl (init := {}) fun m (l, v) => m.insert l v
  let rightMap : Std.HashMap Nat SymExpr :=
    right.env.foldl (init := {}) fun m (l, v) => m.insert l v
  let resultMap : Std.HashMap Nat SymExpr :=
    result.env.foldl (init := {}) fun m (l, v) => m.insert l v
  -- M9.6 (Option C, plan §7.1 #22): strict mode is now the only
  -- mode. When [witnesses] is non-empty (every v2 cert) the
  -- per-entry rule check runs; when [witnesses] is empty (legacy
  -- v1 cert that pre-dated the witnesses field) the join is
  -- accepted without per-entry validation. The [strict] flag is
  -- retained for now; commit #23 removes it altogether.
  let _ := strict
  if !witnesses.isEmpty then
    for entry in witnesses do
      match joinEntryStrictOk leftMap rightMap resultMap entry with
      | none => pure ()
      | some msg => fail msg
      -- M10.x.0 (cert v6): cross-check that `rule` and `delta`
      -- name the same constructor.
      match entry.rule, entry.delta with
      | .joinSame, .trivial => pure ()
      | .joinVar, .trivial => pure ()
      | .joinSymbolic _, .symbolic _ => pure ()
      | .joinMutBorrows _ _ _ _, .mutBorrows _ _ => pure ()
      | .joinBottomOther _, .bottomOther _ => pure ()
      | .joinOtherBottom _, .otherBottom _ => pure ()
      | _, _ => fail s!"E-Join v6: rule {repr entry.rule} and delta {repr entry.delta} name different constructors for local {entry.localId}"
  -- M10.x.10: chain-fold over witnesses (replaces the prior
  -- `addAbsShape` fold + wholesale `result.env.foldl` env-override).
  -- Each step matches `JoinEntryStep.<rule>` and updates env /
  -- absRegistry / HWMs accordingly. Locals not named by any witness
  -- keep their pre-join `st.env` value. The pre-flight scan of all
  -- 89 fixtures (30 joins) confirmed that `result.env` keys are
  -- exactly the witnessed localIds — no information loss from
  -- dropping the wholesale override.
  let st ← witnesses.foldlM (init := st) joinChainFoldStep
  -- Rebuild loans: keep direct kinds we already had, add any new
  -- ids the join's liveLoans list reports. `concretise` does not
  -- read `loans`, so this is invisible to soundness; we keep it
  -- for cert behavior parity.
  let newLoans : Std.HashMap Nat LoanInfo :=
    result.liveLoans.foldl (init := st.loans) fun m b =>
      if m.contains b then m
      else m.insert b { given := .bottom, kind := .reborrow }
  let liveSet : Std.HashSet Nat :=
    result.liveLoans.foldl (init := {}) (·.insert ·)
  let prunedLoans : Std.HashMap Nat LoanInfo :=
    newLoans.fold (init := {}) fun m b li =>
      if liveSet.contains b then m.insert b li
      else if li.kind == .direct then m.insert b li
      else m
  return { st with loans := prunedLoans }

end AeneasCheck.LLBCSharp
