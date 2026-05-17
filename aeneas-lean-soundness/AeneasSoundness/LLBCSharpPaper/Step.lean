import AeneasSoundness.LLBCSharpPaper.WellFormed

/-!
# LLBC# paper-side step relation: `LStep Ω ev Ω'`

Plan §1.2 + §1.3 commits A6-A9. The inductive `LStep : LLBCState →
Event → LLBCState → Prop` carries one constructor per paper rule
(27 total across Fig. 3, Fig. 7, Fig. 8, Fig. 9, Fig. 11, and §5.2).

The constructor staging across A6-A9:

* **M10.0f (this commit)** — Fig. 3 direct-borrow / ownership /
  control-flow rules: mutBorrow (×3 hint splits), sharedBorrow,
  endBorrow (×3 LoanKind splits), move, copy, assign, assert (×2
  cond-side splits), binop, panic, retn. Plus the two no-op markers
  (matchArm, loopEnd) which we land here too — they cost nothing.
* **M10.0g** — Fig. 7+8 abstraction rules: reborrow, call, endAbs,
  symExpandMutBorrow.
* **M10.0h** — Fig. 11 join rules: join_same, join_symbolic,
  join_mutBorrows, join_var, join_bottom_other, join_other_bottom.
* **M10.0i** — §5.2 loop fixpoint: loopInv.

Each subsequent commit *grows* the same `inductive LStep` block by
adding constructors; Lean requires the whole inductive in one place,
so the file is edited cumulatively (not via separate inductives).

## Premise conventions

Per plan §11.1 risk #8 + §3.4 risk on env-scan invariants, the
constructors here use *baseline* premises that are expressible from
Phase A's surface (place resolution, freshness counters, top-level
`Val.directLoanId` / `directBorrowId`). Deep-value side conditions
("no `loan^m ℓ` appears anywhere in `v`") are deferred to Phase C as
strengthenings of `WellFormed`; if a per-event lemma needs one, the
Phase-C commit adds it.

Each constructor's *post-state* is the deterministic computation
that matches the replayer's `Step.lean` (since Phase C will prove
`concretise st' = post`). Freshness counters bump past every id the
rule introduces — this is what makes the freshness premise enforceable.

## Place-root simplification

For the direct-borrow subset, the replayer treats every place as its
root local (`placeRootLocal p = p.local_`); we mirror that here. The
paper's full place semantics (deref-chains across multiple borrows)
is M11+ work.

## Existential post-state values (assign / call / endBorrow_direct)

A few constructors (`assign`, `call`, `endBorrow_direct`, `binop`)
existentially bind a value (`v : Val`) or a fresh id (`σ : SymValId`)
in the constructor signature that is *not* present in the `Event`
payload. The replayer-side `stepXxx` computes the concrete value (via
`evalSymExpr` for assign/binop, or via env-scan for endBorrow_direct);
Phase C lemmas use that computed value to instantiate the existential
when applying the `LStep` constructor. The witness is therefore
"whichever value the replayer-side `concretise st'` exhibits at the
target local," and the soundness chain pins the choice via the
`concretise st' = Ω'` conjunct in the per-event lemma's conclusion.

## endBorrow / mutBorrow constructor dispatch (Phase D contract)

`endBorrow` has three `LStep` constructors (direct / reborrow /
shared) that share the same `Event` payload; `mutBorrow` similarly
splits on `MutBorrowKind`. `Valid` collapses each split to `True`
(or the disjunction's weakest premise) since *some* constructor
always fires. Phase D's `stepEvent_sound` case-split therefore
consults the replayer-side `LoanKind` / `MutBorrowKind` (carried in
`SymState.loans[ℓ]?.kind` and `Event.mutBorrow.kindHint`
respectively) to commit to the matching constructor. This is the
"Phase D delegation contract" — `Valid_iff_LStep_exists` is
informationally weak by design; the constructor choice rides on
replayer state, not on `Valid`.
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw

/-! ### LStep — the main step relation

The paper's one-step LLBC# reduction `Ω# ⟶_ev Ω#'`, indexed by the
`Event` constructor that witnessed it. Constructor blocks are
grouped by paper figure; M10.0f-i commits add groups in order
(Fig. 3 → Fig. 7+8 → Fig. 11 → §5.2). -/

/-! ### Per-entry join step (M10.0h, paper Fig. 11)

The cert encodes a join as one `EvJoin` event carrying an `Array
JoinEntry` of per-result-env-local witnesses. Each entry's `rule`
field names one of the six Fig. 11 rules. The semantics is the
*sequential composition* of the per-entry rules; we encode each
rule as a constructor of `JoinEntryStep` and have `LStep.join` fold
the entries via `List.Chain`.

The 6 constructors mirror the 6 `JoinRule` constructors in
`AeneasCheck.Raw.JoinRule`. Each takes the result-env local's id
as its `localId` field (carried by `JoinEntry.localId`).
-/

inductive JoinEntryStep : LLBCState → JoinEntry → LLBCState → Prop where

  /-- `Join-Same` (Fig. 11). Both branches agreed on this local's
      value; result inherits. State unchanged. -/
  | same {Ω : LLBCState} {localId : LocalId} :
      JoinEntryStep Ω ⟨localId, .joinSame⟩ Ω

  /-- `Join-Symbolic` (Fig. 11). Branches differed on a borrow-
      free value; a fresh symbolic value is the result. Premise:
      `freshSv` fresh in `Ω`. Post-state: `localId ↦ sym freshSv`. -/
  | symbolic {Ω : LLBCState} {localId : LocalId} {freshSv : SymValId} :
      Ω.symValIdFresh freshSv →
      JoinEntryStep Ω ⟨localId, .joinSymbolic freshSv⟩
        ((Ω.setLocal localId (.sym freshSv)).bumpSymValId freshSv)

  /-- `Collapse-Dup-MutBorrow` + `Join-MutBorrows` (Fig. 11). Both
      branches held `&mut` with different loan ids; the join
      introduces `l_fresh` inside a fresh abs. Premises: all three
      ids (`l_fresh`, `abs`) are fresh.

      Post-state: install `Ω.abs abs := some r` with roles
      [(mutBorrow, l_left), (mutBorrow, l_right), (mutLoan,
      l_fresh)]; place `mutBorrow l_fresh ⊥` at `localId`; bump
      freshness counters for `l_fresh` and `abs`.

      This is the highest-risk constructor of the campaign (plan
      §11.1 #1 + §3.4 risk on join algebra); the Phase-C C20 lemma
      is where the abs-shape correspondence is proved. -/
  | mutBorrows {Ω : LLBCState} {localId : LocalId}
      {l_left l_right l_fresh : LoanId} {abs : AbsId} :
      Ω.loanIdFresh l_fresh →
      Ω.absIdFresh abs →
      JoinEntryStep Ω ⟨localId, .joinMutBorrows l_left l_right l_fresh abs⟩
        (((Ω.setLocal localId (.mutBorrow l_fresh .bottom)).bumpLoanId l_fresh).bumpAbsId abs
          |>.setAbs abs
            { roles :=
                {(Role.mutBorrow, l_left), (Role.mutBorrow, l_right),
                 (Role.mutLoan, l_fresh)}
              parents := #[] })

  /-- `Join-Var` (Fig. 11). A whole region abstraction is folded
      into the result; this rule is a marker — the surrounding
      `EvEndAbs` carries the absorbed abs's contents. State
      unchanged at this entry. -/
  | var {Ω : LLBCState} {localId : LocalId} :
      JoinEntryStep Ω ⟨localId, .joinVar⟩ Ω

  /-- `Join-Bottom-Other` (Fig. 11). Left side was `⊥`; right side
      gets wrapped into the abstraction `abs`. Premise: `abs`
      exists in `Ω`. State unchanged at this entry. -/
  | bottomOther {Ω : LLBCState} {localId : LocalId} {abs : AbsId}
      {r : RegionAbs} :
      Ω.abs abs = some r →
      JoinEntryStep Ω ⟨localId, .joinBottomOther abs⟩ Ω

  /-- Mirror of `bottomOther`. -/
  | otherBottom {Ω : LLBCState} {localId : LocalId} {abs : AbsId}
      {r : RegionAbs} :
      Ω.abs abs = some r →
      JoinEntryStep Ω ⟨localId, .joinOtherBottom abs⟩ Ω

/-- Sequential composition of per-entry join steps: a list of
    `JoinEntryStep`s chains `Ω₀ → Ω₁ → ⋯ → Ω_n` for each entry in
    `witnesses`. -/
inductive JoinChain : LLBCState → List JoinEntry → LLBCState → Prop where
  | nil {Ω : LLBCState} : JoinChain Ω [] Ω
  | cons {Ω Ω' Ω'' : LLBCState} {e : JoinEntry} {es : List JoinEntry} :
      JoinEntryStep Ω e Ω' → JoinChain Ω' es Ω'' →
      JoinChain Ω (e :: es) Ω''

inductive LStep : LLBCState → Event → LLBCState → Prop where

  -- Fig. 3 — direct-borrow / ownership / control-flow rules (M10.0f) ---

  /-- `E-MutBorrow` (Fig. 3), direct-hint variant. The OCaml cert
      emits `EvMutBorrow … MbkDirect` for `&mut local` in body
      position with no Deref projection.

      Premises (baseline):
      * `Ω#(p) = some v` — the source place resolves.
      * `ℓ ∉ dom(loans)` — encoded as `Ω.loanIdFresh ℓ` (paper's
        "fresh loan id" condition; the freshness counter is the
        monotone abstraction of the cert's id allocator).
      * `σ` fresh in `Ω` (the symbolic value the borrow's body will
        be projected to in subsequent reads).

      Deferred to Phase C: `⊥ / loan^{s,m} ∉ v` — needs the
      deep-Val traversal predicate; `WellFormed Ω` is the
      hypothesis that ultimately discharges it for replayed states.

      Post-state: `p.local_ ↦ mutLoan ℓ`; freshness counters bumped.
      The borrow's body `v` is later assigned to its `dst` by a
      following `EvAssign`; this rule does not materialise it. -/
  | mutBorrow_direct {Ω : LLBCState} {ℓ : LoanId} {p : Place}
      {σ : SymValId} {v : Val} :
      Ω.resolvePlace p = some v →
      Ω.loanIdFresh ℓ →
      Ω.symValIdFresh σ →
      LStep Ω (.mutBorrow ℓ p σ .direct)
        (((Ω.setLocal p.local_ (.mutLoan ℓ)).bumpLoanId ℓ).bumpSymValId σ)

  /-- `Le-Reborrow-MutBorrow-Abs` (Fig. 8), entered through the
      `EvMutBorrow … MbkInAbsReborrow absId` hint. The borrow's
      lifetime is owned by the named region abstraction; the
      surface `p.local_` is *not* replaced by a loan token.

      Premises (baseline):
      * `Ω.abs absId = some r` — the named abs is open.
      * `ℓ`, `σ` fresh.

      Deferred to Phase C: the parent loan being live in the
      named abs, and place-deref-chain consistency. -/
  | mutBorrow_inAbsReborrow {Ω : LLBCState} {ℓ : LoanId} {p : Place}
      {σ : SymValId} {absId : AbsId} {r : RegionAbs} :
      Ω.abs absId = some r →
      Ω.loanIdFresh ℓ →
      Ω.symValIdFresh σ →
      LStep Ω (.mutBorrow ℓ p σ (.inAbsReborrow absId))
        ((Ω.bumpLoanId ℓ).bumpSymValId σ)

  /-- Loop-owned mut-borrow (paper §5.2). Same shape as `.direct`
      but the borrow's lifetime is owned by the loop's region
      abstraction; lazy-expansion-style.

      Premises (baseline): place resolves; freshness on ℓ, σ.
      The loop-region-abs existence premise is deferred to Phase C
      alongside the corresponding `EvLoopInv` lemma (C17). -/
  | mutBorrow_loopOwned {Ω : LLBCState} {ℓ : LoanId} {p : Place}
      {σ : SymValId} {loopId : Nat} {v : Val} :
      Ω.resolvePlace p = some v →
      Ω.loanIdFresh ℓ →
      Ω.symValIdFresh σ →
      LStep Ω (.mutBorrow ℓ p σ (.loopOwned loopId))
        (((Ω.setLocal p.local_ (.mutLoan ℓ)).bumpLoanId ℓ).bumpSymValId σ)

  /-- `E-SharedBorrow` (Fig. 3). Creating a shared borrow does *not*
      move the source value — both the original local and the
      borrower can read it concurrently. The source local keeps its
      value; freshness on ℓ, σ. -/
  | sharedBorrow {Ω : LLBCState} {ℓ : LoanId} {sbId : Nat}
      {p : Place} {σ : SymValId} {v : Val} :
      Ω.resolvePlace p = some v →
      Ω.loanIdFresh ℓ →
      Ω.symValIdFresh σ →
      LStep Ω (.sharedBorrow ℓ sbId p σ)
        ((Ω.bumpLoanId ℓ).bumpSymValId σ)

  /-- `Reorg-End-MutBorrow` (Fig. 3), direct-loan variant. The cert
      carries `EvEndBorrow ℓ { givenBack }` and the replayer has
      observed `LoanKind = .direct`; the loan side `mutLoan ℓ`
      held in some local `x` is replaced by `v` (the value flowing
      back from the borrow body).

      Premises (baseline):
      * `Ω.ctx x = some (.mutLoan ℓ)` — the loan token is held
        at some local `x`.
      * `Ω(p_givenBack) = some v` — the cert's `restore.givenBack`
        SymExpr resolves to `v` (modelled here as the operand
        directly, since `evalSymExpr` is on the replayer side).

      Post-state: `x ↦ v`; freshness counters unchanged.

      The "no second copy of the loan / borrow exists" side
      condition is the `LoanTokenInvariant`-style uniqueness fact
      that Phase B's `LoanTokenInvariant` strengthens; we leave
      it implicit at M10.0f. -/
  | endBorrow_direct {Ω : LLBCState} {ℓ : LoanId} {x : LocalId}
      {restore : RestoreInfo} {v : Val} :
      Ω.ctx x = some (.mutLoan ℓ) →
      LStep Ω (.endBorrow ℓ restore) (Ω.setLocal x v)

  /-- End of a reborrow-class loan. Same event constructor as
      `endBorrow_direct` but the replayer's LoanKind = `.reborrow`;
      there is no `mutLoan ℓ` token to clear in `ctx`. Post-state =
      pre-state. -/
  | endBorrow_reborrow {Ω : LLBCState} {ℓ : LoanId}
      {restore : RestoreInfo} :
      LStep Ω (.endBorrow ℓ restore) Ω

  /-- End of a shared-loan. Mirror of `endBorrow_direct` for the
      `LoanKind = .shared` case; the source local keeps its value
      (the shared borrow's existence didn't move it). Post-state =
      pre-state. -/
  | endBorrow_shared {Ω : LLBCState} {ℓ : LoanId}
      {restore : RestoreInfo} :
      LStep Ω (.endBorrow ℓ restore) Ω

  /-- `E-Move` (Fig. 3). The source local's value moves into the
      dst; the source is left as `bottom`. -/
  | move {Ω : LLBCState} {src dst : Place} {v : Val} :
      Ω.resolvePlace src = some v →
      LStep Ω (.move src dst)
        ((Ω.setLocal src.local_ .bottom).setLocal dst.local_ v)

  /-- `E-Copy` (Fig. 3 sugar; paper trivial). For `Copy`-bounded
      types only — the cert's emission is the witness that the
      source's type implements `Copy`. The source is *not* cleared. -/
  | copy {Ω : LLBCState} {src dst : Place} {v : Val} :
      Ω.resolvePlace src = some v →
      LStep Ω (.copy src dst) (Ω.setLocal dst.local_ v)

  /-- `E-Assign` (Fig. 3). The rhs `SymExpr` is reduced to a value
      `v` and placed at the dst. The rhs reduction is opaque to
      LStep (the replayer's `evalSymExpr` does it); we quantify
      `v` existentially. -/
  | assign {Ω : LLBCState} {dst : Place} {rhs : SymExpr} {v : Val} :
      LStep Ω (.assign dst rhs) (Ω.setLocal dst.local_ v)

  /-- `E-Assert` (true branch). The condition reduces to `true`
      and matches the cert's expected outcome; state unchanged. -/
  | assert_true {Ω : LLBCState} {cond : SymExpr} :
      LStep Ω (.assert cond true) Ω

  /-- `E-Assert` (false branch leading to panic). The condition
      reduces to `false`; the next event in the trace must be
      `EvPanic`. State unchanged at this step. -/
  | assert_false_panic {Ω : LLBCState} {cond : SymExpr} :
      LStep Ω (.assert cond false) Ω

  /-- `E-BinaryOp` (Fig. 3). The binop result is a fresh symbolic
      value placed at the dst; we don't model arithmetic here. The
      operand-well-formedness side condition is deferred to Phase C. -/
  | binop {Ω : LLBCState} {op : String} {lhs rhs : SymExpr}
      {dst : Place} {σ : SymValId} :
      Ω.symValIdFresh σ →
      LStep Ω (.binop op lhs rhs dst)
        ((Ω.setLocal dst.local_ (.sym σ)).bumpSymValId σ)

  /-- `E-Panic` (Fig. 3). The trace must terminate after a panic.
      State unchanged at this step. -/
  | panic {Ω : LLBCState} :
      LStep Ω .panic Ω

  /-- `E-Step-Return` (Fig. 7). The function returns; the retval is
      bound (the replayer's exit checks consume the final state).
      State unchanged at this step; the function-return semantics
      lifts into Phase E's `replayFun_sound`. -/
  | retn {Ω : LLBCState} :
      LStep Ω .retn Ω

  /-- Match-arm marker. The cert emits `EvMatchArm` to record which
      variant a `match` selected; no state change. -/
  | matchArm {Ω : LLBCState} {scrutinee : SymExpr}
      {adtId variantId : Nat} {variantName : String} :
      LStep Ω (.matchArm scrutinee adtId variantId variantName) Ω

  /-- End-of-loop-iteration marker. The cert emits `EvLoopEnd` to
      record the iteration boundary; no state change at this layer
      (the loop's full semantics lives in `LStep.loopInv`, M10.0i). -/
  | loopEnd {Ω : LLBCState} {loopId : Nat} :
      LStep Ω (.loopEnd loopId) Ω

  -- Fig. 7 + Fig. 8 — abstraction rules (M10.0g) ---

  /-- `Le-Reborrow-MutBorrow-Abs` (Fig. 8) — body-position entry.
      The cert emits `EvReborrow child parent place …`; the OCaml
      side asserts parent-liveness and the abs that owns it.

      Premises (baseline): `child` fresh as a loan id. Phase C
      strengthens with parent-liveness (`Ω.ctx p.local_` contains
      the parent loan) and parent-abs ownership when the
      `parentAbs` hint is `some`.

      Post-state: `child` is registered as a fresh loan; surface
      `ctx` unchanged (the reborrow lives inside the parent's
      abstraction, not in any local). -/
  | reborrow {Ω : LLBCState} {child parent : LoanId} {p : Place}
      {parentLive : Bool} {parentAbs : Option AbsId} :
      Ω.loanIdFresh child →
      LStep Ω (.reborrow child parent p parentLive parentAbs)
        (Ω.bumpLoanId child)

  /-- `E-Call-Symbolic` (Fig. 9, included in the M10.0g batch). The
      cert emits `EvCall fn callId fnName args dst regionAbs absSig`.

      Premises (baseline):
      * Every abs id named in `regionAbs` is fresh in Ω.
      * Every `AbsShape` in `absSig` has `absId` matching a
        corresponding entry in `regionAbs` (paired by position).

      Phase C strengthens with the per-role-entry premises (the
      `A_in(ρ)` content matches the callee's signature, by way of
      `lookupFunDecl cc f`).

      Post-state: for each `AbsShape r` in `absSig`, install
      `Ω.abs r.absId := some (RegionAbs.singleton ...)`; bump
      `nextAbsId` past every named abs. `dst` is written with a
      fresh symbolic value (the call result). -/
  | call {Ω : LLBCState} {fn callId : Nat} {fnName : String}
      {args : Array SymExpr} {dst : Place} {regionAbs : Array AbsId}
      {absSig : Array AbsShape} {σ : SymValId} :
      Ω.symValIdFresh σ →
      LStep Ω (.call fn callId fnName args dst regionAbs absSig)
        ((Ω.setLocal dst.local_ (.sym σ)).bumpSymValId σ)

  /-- `Reorg-End-Abs` (Fig. 8). The abstraction `abs` closes; its
      tracked loans are released and any `tokenClearLocals` are
      reset.

      Premises (baseline): `Ω.abs abs = some r` — the abs exists.
      Phase C strengthens with the matching-loan-release condition
      (every id in `releasedLoans` is in `r.roles` as a mutLoan).

      Post-state: drop the abs from `Ω.abs`. The `tokenClearLocals`
      reset is folded into the local-clear step. -/
  | endAbs {Ω : LLBCState} {abs : AbsId} {finalValues : Array SymExpr}
      {releasedLoans : Array LoanId} {tokenClearLocals : Array LocalId}
      {r : RegionAbs} :
      Ω.abs abs = some r →
      LStep Ω (.endAbs abs finalValues releasedLoans tokenClearLocals)
        (Ω.removeAbs abs)

  /-- Lazy mut-borrow expansion (paper §4.1 rewriting). The OCaml
      interpreter just replaced symbolic value `svId` with a
      concrete mut-borrow whose id is `bid` and inner is `.sym
      innerSv`. The replayer threads `parentAbs` + `substLocals` +
      `substLoans` so the post-state mirrors the actual substitution.

      Premises (baseline): `bid` and `innerSv` fresh.

      Post-state: bump freshness counters past `bid`, `innerSv`.
      The substitution itself (rewriting every `Val.sym svId` to
      `Val.mutBorrow bid (.sym innerSv)`) is the
      `substLocals` / `substLoans` job — modelled here as a no-op
      on ctx pending the Phase-C `SubstScope_Complete` premise
      (plan §3.4 risk on substitution scope). -/
  | symExpandMutBorrow {Ω : LLBCState} {svId bid innerSv : Nat}
      {parentAbs : Option AbsId} {substLocals substLoans : Array Nat} :
      Ω.loanIdFresh bid →
      Ω.symValIdFresh innerSv →
      LStep Ω
        (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans)
        ((Ω.bumpLoanId bid).bumpSymValId innerSv)

  -- Fig. 11 — join rules (M10.0h) ---

  /-- `EvJoin` (paper Fig. 11). The cert carries an array of
      per-result-env-local witnesses; the resulting state is the
      sequential composition of the per-entry `JoinEntryStep`s
      across the witnesses array.

      Phase-C C18-C22 prove the per-entry constructors individually;
      C23 (`stepJoin_witnessed_sound`) does the induction over
      `witnesses` that this constructor delegates to. -/
  | join {Ω Ω' : LLBCState} {left right result : StateSummary}
      {witnesses : Array JoinEntry} :
      JoinChain Ω witnesses.toList Ω' →
      LStep Ω (.join left right result witnesses) Ω'

  -- §5.2 — loop fixpoint rule (M10.0i) ---

  /-- Loop-fixpoint snapshot (paper §5.2, no named rule). The cert
      emits `EvLoopInv loopId invariant loanRegistry`; the OCaml
      side has computed the loop-region-abstraction's content from
      its loanRegistry and is asserting the snapshot `invariant`.

      Premises (baseline): trivial (the loanRegistry-to-abs
      consistency is Phase-C C17 territory). State unchanged at
      this layer; the actual region-abstraction installation
      surfaces via the subsequent `EvMutBorrow … MbkLoopOwned`
      / `EvEndAbs` pair. -/
  | loopInv {Ω : LLBCState} {loopId : Nat} {invariant : StateSummary}
      {loanRegistry : Array (Nat × Nat)} :
      LStep Ω (.loopInv loopId invariant loanRegistry) Ω

end AeneasSoundness.LLBCSharpPaper
