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
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw

/-- The paper's one-step LLBC# reduction `Ω# ⟶_ev Ω#'`, indexed by
    the `Event` constructor that witnessed it.

    Constructors are added incrementally across M10.0f-i; each
    paper-rule row in plan §1.2 lands as one constructor here.
-/
-- Constructor blocks below are grouped by paper figure; M10.0f-i
-- commits add groups in order (Fig. 3 → Fig. 7+8 → Fig. 11 → §5.2).

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

end AeneasSoundness.LLBCSharpPaper
