import AeneasCheck.Raw.Places
import AeneasCheck.Raw.Literal

/-!
Raw certificate events — Lean mirror of `src/cert/CertEvent.ml`.

Direct-borrow subset (M2-M8): mutBorrow, sharedBorrow, assign, move,
copy, endBorrow, assert, panic, return. The rest are stubs that parse
but the replayer rejects in milestone-specific ways.

M9.6 (Option C): rule-choice hints are layered onto existing event
constructors as optional fields with back-compat defaults — see the
`MutBorrowKind` / `JoinRule` / `AbsRoleEntry` / `AbsShape` block
below and the per-constructor `M9.6` docstrings.
-/

namespace AeneasCheck.Raw

/-- A symbolic value reference or constant in a cert event RHS. -/
inductive SymExpr
  | symVal (id : Nat)
  | symLit (l : Lit)
  | symCopy (p : Place)
  | symMove (p : Place)
  | symMutBorrowTok (borrowId : Nat)
  /-- M9.5d / M9.5f: an enum variant construction. `adtId` keys into the
      crate's `typeDecls` table; `variantName` is the bare constructor
      name. Used as the RHS of an `EvAssign` whose Charon source was
      a variant `AggregatedAdt`.

      M9.5d covered only the nullary case (empty [fields]); M9.5f
      extends this with one [SymExpr] per payload field. The Lean
      emitter renders nullary variants as `<adtName>.<variantName>`
      and payload-bearing ones as
      `<adtName>.<variantName> <e1> ... <eN>` (with the qualification
      resolved via the type-decl map). -/
  | symVariant (adtId variantId : Nat) (variantName : String)
               (fields : Array SymExpr)
  /-- M9.5p: a tuple aggregate construction, e.g. `(x, y)` on the RHS
      of an `EvAssign`. The Lean translator renders this as
      `(e1, e2, …, eN)`. -/
  | symTuple (fields : Array SymExpr)
  /-- M9.5p: a named-field struct aggregate construction, e.g.
      `Pair { x, y }`. Each entry carries the field's surface name as
      resolved by the OCaml cert generator (using the type-decl's
      `field_name`; tuple-style structs fall back to `fieldK`). The
      Lean translator renders this as `{ x := e1, y := e2 }`. -/
  | symRecord (adtId : Nat) (fields : Array (String × SymExpr))
  deriving Repr

/-- Restoration info for an EvEndBorrow event.

    M10.x.0 (cert v6): `holderLocal` names the env local whose
    `mutLoan` token the end-borrow restores. Populated by the
    OCaml emitter for `.direct`/`.lazyExpand` kinds (via an
    `eval_ctx.env` walk at `InterpBorrows.ml:1050`); `none` for
    `.reborrow`/`.shared` kinds and as a sentinel when no local
    holds the token. Not yet consumed by the replayer at
    M10.x.0 — it lands here as schema plumbing for M10.x.9,
    which inverts the env-walk in `stepEndBorrow .direct /
    .lazyExpand` into a direct `setLocal`. -/
structure RestoreInfo where
  givenBack : SymExpr
  holderLocal : Option Nat := none
  deriving Repr

/-- A coarse summary of state at a point in evaluation. -/
structure StateSummary where
  env : Array (Nat × SymExpr)
  liveLoans : Array Nat
  deriving Repr, Inhabited

/-! ## Option C (M9.6) hint schema

These types are the Lean mirror of the JSON hints introduced in
`cert_fmt_version = 2`. They are carried as optional fields on the
existing `Event` constructors (with defaults that preserve the
pragmatic behaviour of v1 certs). The Lean checker's "strict path"
(landed across plan §7.1 commits #13-#23) consumes them; the JSON
parser fills the defaults for any v1 cert or any v2 cert that omits
the field. See `documentation/option-c-implementation-plan.md` §1 for
the per-field specification and `documentation/cert-format-and-soundness.md`
§3.2 for the pragmatic shortcuts each hint eliminates. -/

/-- M9.6: classification of an `EvMutBorrow`. Subsumes the
    pragmatic M9.5w (Deref-projection ⇒ reborrow-class) and M9.5aa
    (in-loop ⇒ lazyExpand) shortcuts:

    * `direct` — in-body `&mut p` with no Deref in its projection
      and no enclosing loop; must be explicitly ended before
      function exit.
    * `inAbsReborrow absId` — a `&mut (*x).f`-shaped borrow whose
      lifetime is owned by the named region abstraction (typically
      a caller-input abstraction); allowed to leak past exit.
    * `loopOwned loopId` — a direct `&mut local` issued inside an
      open loop body; the loop's region abstraction owns its
      lifetime. -/
inductive MutBorrowKind
  | direct
  | inAbsReborrow (absId : Nat)
  | loopOwned (loopId : Nat)
  deriving Repr, Inhabited

/-- M9.6: per-`avalue` role of a `tavalue` inside a function-call's
    input region abstraction (paper §4.1 `A_in(ρ)` content). Carried
    inside `AbsShape.roles`. -/
inductive AbsRoleEntry
  /-- The abstraction holds a mutable input borrow whose loan id is
      `loanId`; `argIdx` is the call-site argument position the
      borrow originated from. -/
  | mutBorrow (argIdx : Nat) (loanId : Nat)
  /-- The abstraction owns the loan side of `loanId` — i.e. when the
      abstraction ends, the loan is released and any held
      `mutLoan loanId` token is cleared. -/
  | mutLoan (loanId : Nat)
  /-- A shared borrow owned by the abstraction. -/
  | sharedBorrow (argIdx : Nat) (sharedBorrowId : Nat)
  deriving Repr, Inhabited

/-- M9.6: the shape of one region abstraction freshened by `EvCall`.
    Mirrors the paper's `A_in(ρ) { borrow^m ℓ _, loan^m ℓ' }` shape:
    an abstraction id, its ancestor ids (for nested-borrow contracts),
    and one `AbsRoleEntry` per `tavalue` held.

    M9.8 (cert v4): also carried by `JoinRule.joinMutBorrows` for the
    fresh region abstraction created by Collapse-Dup-MutBorrow, so
    `stepJoin` can install it in `absRegistry` symmetric to how
    `stepCall` already installs `EvCall.abs_sig` shapes. -/
structure AbsShape where
  absId : Nat
  parentAbs : Array Nat
  roles : Array AbsRoleEntry
  deriving Repr, Inhabited

/-- M9.6: per-local witness of which Fig. 11 (paper) rule the OCaml
    interpreter applied to derive a `EvJoin` result entry. Carried
    inside `JoinEntry`; one entry per result-env local in declaration
    order. -/
inductive JoinRule
  /-- Both branches agreed on this local's value. -/
  | joinSame
  /-- Branches differed on a value containing no borrows/loans; the
      OCaml side introduced a fresh symbolic value `freshSv` and the
      result is `SymVal freshSv`. -/
  | joinSymbolic (freshSv : Nat)
  /-- Both branches held a `&mut` with different loan ids; the join
      introduced a fresh borrow id `l_fresh` inside a fresh region
      abstraction `abs` (Collapse-Dup-MutBorrow).

      M9.8 (cert v4): `abs` is the full `AbsShape` (id + parents +
      roles), not just an `AbsId`. The Lean replayer's `stepJoin`
      installs the abs in `SymState.absRegistry` using this shape,
      mirroring how `stepCall` already installs `EvCall.abs_sig`'s
      shapes. The soundness side then has the fresh abs's content
      by construction, closing the C23
      `stepJoin_witnessed_sound` general case (M10 plan §11.1 #1
      / §3.4 / §14.1). By construction `abs.parentAbs = #[]` and
      `abs.roles` is the three-entry list
      `[mutBorrow _ l_left, mutBorrow _ l_right, mutLoan l_fresh]`. -/
  | joinMutBorrows (l_left l_right l_fresh : Nat) (abs : AbsShape)
  /-- `Join-Var` rule (paper Fig. 11): a whole region abstraction is
      folded into the result. (Marker only in this milestone; the
      surrounding `EvEndAbs` carries the absorbed abstraction's
      contents.) -/
  | joinVar
  /-- Left side is `⊥`; right side is wrapped into the abstraction
      `abs`. -/
  | joinBottomOther (abs : Nat)
  /-- Mirror of `joinBottomOther`. -/
  | joinOtherBottom (abs : Nat)
  deriving Repr, Inhabited

/-- M10.x.0 (cert v6): per-`JoinEntry` delta witness. Captures only
    the `JoinEntryStep` premise the paper-side constructor needs —
    never the full intermediate `Ω_i` state. Intermediate states
    are rebuilt in Lean by folding deltas
    (`Soundness/JoinLemmas.joinChain_of_witnesses`, landing at
    M10.x.10). The constructor names are parallel to `JoinRule`;
    the replayer cross-checks the pair in `stepJoin`. -/
inductive JoinEntryDelta
  /-- Matches `JoinSame` / `JoinVar`: no state change, no
      freshness premise. -/
  | trivial
  /-- Matches `JoinSymbolic n`: post-state introduces `SymVal n`;
      the freshness premise is the HWM fact `Ω_i.symValIdFresh n`. -/
  | symbolic (freshSv : Nat)
  /-- Matches `JoinMutBorrows`: the freshness premise is
      `Ω_i.loanIdFresh l_fresh ∧ Ω_i.absIdFresh absId`. -/
  | mutBorrows (l_fresh : Nat) (absId : Nat)
  /-- Matches `JoinBottomOther abs`: the abs must be live in
      `Ω_i.abs`. -/
  | bottomOther (absId : Nat)
  /-- Mirror of `bottomOther`. -/
  | otherBottom (absId : Nat)
  deriving Repr, Inhabited

/-- M9.6: one entry of `EvJoin.witnesses`.

    M10.x.0 (cert v6): `delta` is the parallel `JoinEntryStep`
    premise carrier. The replayer cross-checks that `rule` and
    `delta` name the same constructor; the redundancy lets
    Lean perform the chain fold in `JoinLemmas` without
    case-matching on `JoinRule` from outside that module. -/
structure JoinEntry where
  localId : Nat
  rule : JoinRule
  delta : JoinEntryDelta := .trivial
  deriving Repr, Inhabited

/-- LLBC# trace events. Constructor names match `CertEvent.event`
    (without the `Ev` prefix). -/
inductive Event
  -- direct-borrow subset
  /-- M9.6 `kindHint` (Option C) subsumes M9.5w + M9.5aa: the OCaml
      side declares whether this `&mut` is direct, reborrow-class
      (held inside a named region abstraction), or loop-owned.
      Defaults to `.direct` for back-compat with pre-M9.6 certs;
      the M9.5w/aa pragmatic inference in `Step.lean` is the
      fallback while the hint is absent. -/
  | mutBorrow (loan : Nat) (place : Place) (symval : Nat)
              (kindHint : MutBorrowKind := .direct)
  | sharedBorrow (loan : Nat) (sharedBorrowId : Nat) (place : Place) (symval : Nat)
  | assign (dst : Place) (rhs : SymExpr)
  | move (src dst : Place)
  | copy (src dst : Place)
  | endBorrow (loan : Nat) (restore : RestoreInfo)
  | assert (cond : SymExpr) (expected : Bool)
  | panic
  | retn
  /-- M10.0: a Charon `Rvalue.BinaryOp` reduction. `op` is the flat
      string tag emitted by OCaml's `cert_binop_string` (arithmetic
      ops bake the overflow mode in: `AddPanic` / `AddWrap` /
      `AddUB`, etc.). -/
  | binop (op : String) (lhs rhs : SymExpr) (dst : Place)
  -- later milestones
  /-- M9.6 `parentLive` / `parentAbs` (Option C): the OCaml side
      asserts whether the parent borrow is still live in the
      caller-state (`parentLive = true` requires
      `st.loans.contains parent`) and which abstraction owns it.
      Defaults to `false` / `none` for back-compat — the
      `stepReborrow` pragmatic "pre-add a fake `.reborrow` parent
      if missing" branch is the fallback while the hints are
      absent. -/
  | reborrow (child parent : Nat) (place : Place)
             (parentLive : Bool := false)
             (parentAbs : Option Nat := none)
  /-- M10.1: a function call. `fnName` is the qualified callee name
      (e.g. `core::num::{u32}::wrapping_add`); the translator
      consumes it directly so we don't need a builtin-id lookup
      table. `regionAbs` is the abstraction-id list that M10.2's
      End-Abstraction rule consumes.

      M9.6 `absSig` (Option C): one `AbsShape` per region
      abstraction freshened by this call (one-to-one with
      `regionAbs`). Encodes the paper's `A_in(ρ)` content (per-arg
      mut/shared borrows the call owns + the loan ids whose
      lifetime flows into the abstraction). Defaults to empty for
      back-compat — while absent, abstraction ids stay opaque
      tokens and `EvEndAbs.releasedLoans` alone drives release. -/
  | call (fn callId : Nat) (fnName : String) (args : Array SymExpr)
      (dst : Place) (regionAbs : Array Nat)
      (absSig : Array AbsShape := #[])
  /-- M10.2 / M9.5s: a region abstraction just closed. `finalValues`
      carries one symbolic-value reference per [AEndedMutBorrow] the
      abstraction held, in left-to-right order — the Forward
      translator pairs each entry with the most recent EvCall's
      [region_abs] field to bind post-state names. `releasedLoans`
      (M9.5s) lists the loan ids whose lifetime the abstraction owned
      and which the OCaml interpreter implicitly ended when destroying
      the abstraction (paper.rs `call_choose` pattern: input borrows
      that flowed into the call's abstraction and were never
      explicitly ended via [EvEndBorrow]). The Lean replayer drops
      each released loan from [SymState.loans] and the typechecker
      moves it from [liveLoans] to [endedLoans], so the
      "function ended with live borrow(s)" post-condition passes for
      these implicitly-ended loans. Defaults to empty for back-compat
      with pre-M9.5s certs.

      M9.6 `tokenClearLocals` (Option C) strengthens
      `releasedLoans`: explicitly lists the locals whose `mutLoan`
      token must be cleared when this abstraction ends. Defaults
      to empty — while absent, `stepEndAbs` falls back to the
      scan-env behaviour. -/
  | endAbs (abs : Nat) (finalValues : Array SymExpr)
           (releasedLoans : Array Nat := #[])
           (tokenClearLocals : Array Nat := #[])
  | proj (abs : Nat) (place : Place) (symval : Nat)
  /-- M9.5r: lazy mut-borrow expansion. The OCaml interpreter just
      replaced symbolic value `svId` (some [&mut T]-typed value) with
      a concrete mut-borrow whose id is `bid` and whose inner value is
      a fresh symbolic value `innerSv`. The Lean replayer scans every
      local / loan-given holding `.sym svId`, replaces with `.mutLoan
      bid`, and registers loan `bid` with `given := .sym innerSv` —
      so a subsequent in-body `EvEndBorrow loan=bid` (paper.rs
      `test_choose` pattern) can resolve.

      M9.6 `parentAbs` / `substLocals` / `substLoans` (Option C)
      eliminate the M9.5r env-scan: `parentAbs` names the
      abstraction that owns the now-expanded borrow, `substLocals`
      lists every env local whose value was `.sym svId` (and is
      now `.mutLoan bid`), and `substLoans` lists every loan-given
      slot that was likewise rewritten. All default to empty/none
      for back-compat. -/
  | symExpandMutBorrow (svId bid innerSv : Nat)
                       (parentAbs : Option Nat := none)
                       (substLocals : Array Nat := #[])
                       (substLoans : Array Nat := #[])
  /-- M9.6 `witnesses` (Option C): per-result-env-local rule
      witness from the join algebra (paper Fig. 11). When
      non-empty, drives the strict per-entry check; when empty,
      `stepJoin` falls back to the pragmatic
      `symExprBeq` + `isFreshSym` shortcut (M9.5y). -/
  | join (left right result : StateSummary)
         (witnesses : Array JoinEntry := #[])
  /-- M9.6 `loanRegistry` (Option C): explicit
      `(borrowId, parentAbsId)` registry from the OCaml side's
      `compute_loop_entry_fixed_point` output. When non-empty,
      `Replay.stepEvent` for `loopInv` consumes it directly
      (M9.5z scan-env fallback retained while empty). -/
  | loopInv (loopId : Nat) (invariant : StateSummary)
            (loanRegistry : Array (Nat × Nat) := #[])
  /-- M12.1: end-of-loop-body marker. Paired with the preceding
      `loopInv` carrying the same `loopId`; the events between the
      pair form the canonical loop body that the Lean translator
      lifts into a `<fn>_loop.body` decl. -/
  | loopEnd (loopId : Nat)
  /-- M9.5d: per-arm marker for a `match` on a symbolic ADT
      scrutinee. The `scrutinee` is the cert sym-expr for the
      matched value (typically `SymVal` of the symbolic id that
      was expanded). `variantId` / `variantName` identify which
      arm follows. The arm's body events run until the next
      `matchArm` for the same scrutinee, the closing `EvJoin`, or
      an `EvReturn` at depth 0. -/
  | matchArm (scrutinee : SymExpr) (adtId variantId : Nat) (variantName : String)
  deriving Repr, Inhabited

/-- A source span attached to a cert function. Used by the Lean
    emitter to build the per-function `Source: ...` docstring. -/
structure SourceSpan where
  file : String
  begLine : Nat
  begCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, Inhabited

/-- M9.5o: one trait obligation on a generic parameter, e.g.
    `T: Trait1` lowers to `{ traitQualifiedName := "crate::Trait1",
    typeParamIdx := 0 }`. The qualified name is what the cert
    carries (rendered against the `traitDecls` table later to derive
    the bare trait name). -/
structure TraitClause where
  traitQualifiedName : String
  typeParamIdx : Nat
  deriving Repr, Inhabited

/-- M10.x.0 (cert v6): reference to a sub-statement in the cert's
    embedded LLBC body tree. `funId` indexes
    `cc.llbcProgram.funDecls`; `bodyPath` is the per-level path
    from the function-body root (e.g. `#[0, 2, 1]` = then-branch of
    stmt 0, nested stmt 2, sub-stmt 1).

    Carried by `FunCert.stmtRefs` as a parallel-to-events array of
    `Option StmtRef`. Phase-E2's `replayFun_event_induct` consumes
    this to interleave with the LLBC body tree rather than the flat
    event list. Not load-bearing for the v6 axiom-elimination
    campaign; lands at M10.x.0 alongside `JoinEntryDelta` /
    `RestoreInfo.holderLocal` so the schema bump only happens once. -/
structure StmtRef where
  funId : Nat
  bodyPath : Array Nat
  deriving Repr, Inhabited

/-- Per-function cert trace.

    M9.7o-E5b: the flat `signature : FnSignature` field was deleted
    once the structured `LlbcSignature` (sourced from
    `cc.llbcProgram.funDecls[k].signature`) became the sole carrier
    of typed signature info. The Driver pairs each `FunCert` with
    its matching `LlbcFunDecl` by `fnId` and threads the structured
    signature through to the translator. -/
structure FunCert where
  fnId : Nat
  fnName : String
  /-- `none` when the OCaml side could not attach a span (synthetic
      items, builtins). -/
  sourceSpan : Option SourceSpan
  events : Array Event
  finalState : StateSummary
  /-- M9.5l: optional Lean-shaped name pre-computed by the OCaml
      cert generator. Set for trait-impl method bodies (e.g.
      `Tag.Insts.Traits_basicNumeric.value`); `none` for regular
      functions, in which case the emitter falls back to sanitizing
      `fnName`. The translator threads this through the `EvCall`
      callee lookup so caller sites see the same pretty name. -/
  prettyName : Option String := none
  /-- M10.x.0 (cert v6): parallel-to-`events` array of LLBC body-tree
      back-pointers; `none` for synthetic events (loop-fixpoint
      markers, frame-pop end-borrows, etc.). The OCaml emitter
      currently populates with all-`none` sentinels; M10.x.0b will
      thread real `StmtRef`s through the 23 emit sites. Consumed
      by Phase-E2's `replayFun_event_induct`; not load-bearing for
      the v6 axiom-elimination campaign. -/
  stmtRefs : Array (Option StmtRef) := #[]
  deriving Repr, Inhabited

/- M9.7c: `CrateCert` lives in `Raw/LLBCProgram.lean` — moved there to
   carry the new structured `llbcProgram : LlbcProgram` field (cert v3)
   without inducing a cycle (CertEvent ← LLBCProgram).

   M9.7o-E5a: the flat type/trait decl mirrors (`TypeDecl`, `TraitDecl`,
   `TraitImpl`, `CertField`, `CertVariant`, `TypeDeclKind`,
   `TraitMethodDecl`, `TraitImplMethod`) were deleted from this file
   once cert v2 was dropped — the structured `LlbcProgram` subtree
   (`Raw/LLBCProgram.lean`) is now the sole source for these decls. -/

end AeneasCheck.Raw
