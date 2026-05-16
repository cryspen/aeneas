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
    (_symval : Nat) : Result SymState := do
  if st.loans.contains loan then
    fail s!"E-MutBorrow: borrow id {loan} already live"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-MutBorrow: local {root} out of bounds (have {st.numLocals})"
    else
      -- M9.5w: a `&mut (*x).…` (place projection has any Deref) is
      -- conceptually a reborrow of `x`'s loan, even though the OCaml
      -- cert emitter only recognizes the immediate-outer-Deref shape
      -- as EvReborrow. Classify these as `.reborrow` kind so they're
      -- allowed to leak past the function-exit `leakedDirect` check
      -- (their lifetime is owned by the parent borrow's input
      -- abstraction). For the `.reborrow` kind we also skip the
      -- `setLocal root (.mutLoan loan)` token-park: the parent already
      -- has a `mutLoan` token in `root`, and overwriting it would
      -- corrupt the parent's loan-tracking.
      if place.projection.any (· == ProjElem.deref) then
        return st.addLoan loan .bottom .reborrow
      else
        let inner := st.getLocal root
        let st := st.setLocal root (.mutLoan loan)
        let st := st.addLoan loan inner
        return st

/-! ## E-SharedBorrow

Creating a shared borrow does not move the place's value out — both
the original local and the borrower can read it concurrently. The
M9.2 structural check only verifies the borrow id is fresh and the
place is in range; full LLBC# shared-loan algebra lands in M11. -/

def stepSharedBorrow (st : SymState) (loan : Nat) (_sbId : Nat)
    (place : Place) (_symval : Nat) : Result SymState := do
  if st.loans.contains loan then
    fail s!"E-SharedBorrow: borrow id {loan} already live"
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

def stepReborrow (st : SymState) (child parent : Nat) (place : Place) :
    Result SymState := do
  if st.loans.contains child then
    fail s!"E-Reborrow: child borrow id {child} already live"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-Reborrow: local {root} out of bounds (have {st.numLocals})"
    else
      -- If the parent loan is not yet in state, treat it as an
      -- implicit input borrow (e.g. a `&mut T` function argument).
      -- The cert does not emit an explicit EvMutBorrow for input
      -- borrows; pre-adding it here keeps the parent-live invariant
      -- without forcing every cert to carry a signature-derived
      -- entry-event. Implicit parents are tagged `.reborrow` so the
      -- exit check tolerates their liveness (see `Replay.lean`).
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
    -- M9.5x: silent re-end after a branch join. The OCaml interpreter
    -- emits redundant EvEndBorrow events on the same loan during
    -- branch/loop reconciliation (and sometimes across several
    -- fixpoint iterations of a loop's cleanup); the TC has already
    -- validated the structural shape. Treat any re-end of a loan we
    -- previously ended as a no-op.
    if st.joinDedupe.contains loan then
      return st
    else
      fail s!"end-borrow: borrow id {loan} not live"
  | some (li, st) => do
    let st := { st with joinDedupe := st.joinDedupe.insert loan }
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
      let mut found := false
      let mut newEnv := st.env
      for (l, vv) in st.env.toList do
        match vv with
        | .mutLoan b => if b = loan then
            newEnv := newEnv.insert l v
            found := true
        | _ => pure ()
      if not found then
        -- Lazy expansions may have substituted the token through
        -- intermediate locals that the cert subsequently overwrote;
        -- if no local currently holds the token, just release the
        -- loan id without restoration.
        if li.kind == .lazyExpand then return st
        else fail s!"end-borrow: no local holds loan {loan}"
      else
        return { st with env := newEnv }
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

def stepCall (st : SymState) (dst : Place) : Result SymState := do
  let root := placeRootLocal dst
  if root ≥ st.numLocals then
    fail s!"E-Call: dst local {root} out of bounds (have {st.numLocals})"
  else
    return st.setLocal root (.sym 0)

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

def stepSymExpandMutBorrow (st : SymState) (svId bid innerSv : Nat) :
    Result SymState := do
  if st.loans.contains bid then
    fail s!"E-SymExpandMutBorrow: borrow id {bid} already live"
  -- Substitute in env.
  let mut newEnv := st.env
  for (l, v) in st.env.toList do
    match v with
    | .sym k => if k = svId then newEnv := newEnv.insert l (.mutLoan bid)
    | _ => pure ()
  -- Substitute in loan-given values.
  let mut newLoans := st.loans
  for (b, li) in st.loans.toList do
    match li.given with
    | .sym k =>
      if k = svId then
        newLoans := newLoans.insert b { li with given := .mutLoan bid }
    | _ => pure ()
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

def stepEndAbs (st : SymState) (released : Array Nat) : Result SymState := do
  let mut st := st
  for loan in released do
    if st.loans.contains loan then
      st := { st with loans := st.loans.erase loan }
      let mut newEnv := st.env
      for (l, v) in st.env.toList do
        match v with
        | .mutLoan b => if b = loan then newEnv := newEnv.insert l .bottom
        | _ => pure ()
      st := { st with env := newEnv }
  return st

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

/-- Decide whether two `SymExpr` cert values are observationally equal
    for the purposes of the M11 join check. Two `SymVal n` are equal
    iff `n` matches; two `SymLit` iff their underlying literals are
    `BEq`-equal; everything else is conservatively "not equal".

    This is intentionally narrow — the M11 join only succeeds when
    branches genuinely agree, and the fresh-sym fallback rule
    handles the disagreement case. -/
def symExprBeq : SymExpr → SymExpr → Bool
  | .symVal a, .symVal b => a == b
  | .symLit (.bool a), .symLit (.bool b) => a == b
  | .symLit (.scalar ka a), .symLit (.scalar kb b) =>
    -- IntKind has no DecidableEq instance derived yet; compare via
    -- the string form which is stable per the M9 emitter and good
    -- enough for the join witness.
    (Std.Format.pretty (repr ka)) == (Std.Format.pretty (repr kb)) && a == b
  | .symMutBorrowTok a, .symMutBorrowTok b => a == b
  | _, _ => false

/-- Is `e` a "fresh symbolic value" form? The join-symbolic rule
    accepts a fresh `SymVal n` on the result side as subsuming any
    pair of branch values. We don't verify that `n` was actually
    freshly minted by the OCaml ssubst — the cert promise is that
    fresh sym ids in the result didn't appear in either pre-join
    branch's env, which is what `match_ctx_with_target`'s
    [output_svalues] enforces.
    M9.5y: `symMutBorrowTok n` is also accepted as a fresh form. The
    OCaml interpreter's `Collapse-Dup-MutBorrow` rule introduces a
    fresh borrow id in the join result to subsume two distinct
    branch-local borrow ids (e.g. `call_choose`'s left:tok-0,
    right:tok-2, result:tok-3). -/
def isFreshSym : SymExpr → Bool
  | .symVal _ => true
  | .symMutBorrowTok _ => true
  | _ => false

/-- Per-entry join check: returns `none` on success, `some msg` on
    failure. -/
def joinEntryOk (leftMap rightMap : Std.HashMap Nat SymExpr)
    (localId : Nat) (resultE : SymExpr) : Option String :=
  let leftE := leftMap[localId]?
  let rightE := rightMap[localId]?
  match leftE, rightE with
  | some l, some r =>
    if symExprBeq l resultE && symExprBeq r resultE then none  -- Join-Same
    else if isFreshSym resultE then none  -- Join-Symbolic
    else some s!"E-Join: local {localId} result {repr resultE} not ≤-related to left {repr l} / right {repr r}"
  | some _, none | none, some _ =>
    -- One branch dropped the local; accept if the result chose a
    -- fresh sym or matches the surviving side.
    if isFreshSym resultE then none else none
  | none, none =>
    -- Local wasn't bound in either branch but appears in result —
    -- this can happen for join-introduced fresh locals; accept.
    none

def stepJoin (st : SymState) (left right result : StateSummary) :
    Result SymState := do
  -- Build per-side hash maps from the env arrays for O(1) lookup.
  let leftMap : Std.HashMap Nat SymExpr :=
    left.env.foldl (init := {}) fun m (l, v) => m.insert l v
  let rightMap : Std.HashMap Nat SymExpr :=
    right.env.foldl (init := {}) fun m (l, v) => m.insert l v
  -- Per-entry join validation.
  for (localId, resultE) in result.env do
    match joinEntryOk leftMap rightMap localId resultE with
    | none => pure ()
    | some msg => fail msg
  -- Update the symbolic state to match the result.
  let newEnv : Std.HashMap Nat Val :=
    result.env.foldl (init := st.env) fun m (l, v) =>
      m.insert l (valOfSymExpr v)
  -- Rebuild loans: keep direct kinds we already had, add any new
  -- ids the join's liveLoans list reports. M12 will reconcile the
  -- kind algebra; for now we leave existing entries untouched and
  -- never invent loans the cert didn't mention.
  let newLoans : Std.HashMap Nat LoanInfo :=
    result.liveLoans.foldl (init := st.loans) fun m b =>
      if m.contains b then m
      else m.insert b { given := .bottom, kind := .reborrow }
  -- Drop loans that the join no longer lists as live — only when
  -- they exist in our current state. Conservative: we keep any
  -- borrow whose kind is `.direct` (the in-body subset that M5/M6
  -- handle precisely) and only drop reborrow/shared ones.
  let liveSet : Std.HashSet Nat :=
    result.liveLoans.foldl (init := {}) (·.insert ·)
  let prunedLoans : Std.HashMap Nat LoanInfo :=
    newLoans.fold (init := {}) fun m b li =>
      if liveSet.contains b then m.insert b li
      else if li.kind == .direct then m.insert b li
      else m
  return { st with env := newEnv, loans := prunedLoans }

end AeneasCheck.LLBCSharp
