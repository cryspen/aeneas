import AeneasSoundness.Soundness.Concretise.Defn

/-!
# Concretise lemmas: inversion + commute

Plan §2.2 B4 (inversion) + B5 (commute). These lemmas let Phase C
per-event proofs *push `concretise` through* the replayer's state
mutators: every Phase-C lemma's last step is showing `concretise
st' = Ω'`, and the proof discharges by chaining a commute lemma
that says `concretise (mutator st …) = mutator# (concretise st)
…` plus the `Ω'`-witness picked from the `LStep` constructor.

## Inversion lemmas (B4)

Read the structure of `(concretise st)` field by field. Each is a
direct consequence of the `concretise` definition.

## Commute lemmas (B5)

For each `SymState` mutator (`setLocal`, `addLoan`, `takeLoan`),
prove that lifting commutes with the mutation. M10.1e lands these;
M10.1d lands the inversion lemmas first since the commutes use
them.
-/

namespace AeneasSoundness.Soundness.Concretise

open AeneasCheck.LLBCSharp
open AeneasSoundness.LLBCSharpPaper (LLBCState NonceCounters)

/-! ## Inversion lemmas (M10.1d) -/

/-- `concretise st`'s `ctx` projection equals `liftEnv st.env`. -/
@[simp]
theorem concretise_ctx (st : SymState) :
    (concretise st).ctx = liftEnv st.env := rfl

/-- `concretise st`'s `abs` projection equals
    `liftAbsRegistry st.absRegistry`. -/
@[simp]
theorem concretise_abs (st : SymState) :
    (concretise st).abs = liftAbsRegistry st.absRegistry := rfl

/-- `concretise st`'s freshness counters. -/
@[simp]
theorem concretise_freshness (st : SymState) :
    (concretise st).freshness =
      { nextLoanId := maxKeyPlusOne st.loans
        nextAbsId := maxKeyPlusOne st.absRegistry
        nextSymValId := 0 } := rfl

/-- Per-local inversion: reading a local from `concretise st`'s
    `ctx` is `(st.env[l]?).map liftVal`. -/
@[simp]
theorem concretise_ctx_apply (st : SymState) (l : Nat) :
    (concretise st).ctx l = (st.env[l]?).map liftVal := rfl

/-- Per-abs inversion: reading an abs from `concretise st`'s
    `abs` is `(st.absRegistry[a]?).map liftAbsShape`. -/
@[simp]
theorem concretise_abs_apply (st : SymState) (a : Nat) :
    (concretise st).abs a = (st.absRegistry[a]?).map liftAbsShape := rfl

/-! ## HashMap inversion lemmas

Two small helpers tying `liftEnv` to `Function.update` so the
`setLocal` commute below reduces by `funext` + per-key case-split.
-/

/-- `liftEnv (env.insert l v)` is the function-update of
    `liftEnv env` at `l` with `some (liftVal v)`. Used by the
    `setLocal` commute lemma. -/
theorem liftEnv_insert (env : Std.HashMap Nat AeneasCheck.LLBCSharp.Val)
    (l : Nat) (v : AeneasCheck.LLBCSharp.Val) :
    liftEnv (env.insert l v) = Function.update (liftEnv env) l (some (liftVal v)) := by
  funext l'
  unfold liftEnv
  by_cases h : l = l'
  · subst h; simp [Function.update]
  · simp [Std.HashMap.getElem?_insert, h, Function.update_of_ne (Ne.symm h)]

/-! ## Commute lemmas (M10.1e)

For each `SymState` mutator, prove `concretise` commutes with the
matching paper-side mutator. Phase C per-event lemmas chain these
to discharge the `concretise st' = Ω'` conjunct.
-/

/-- `setLocal` commute: `concretise (st.setLocal l v) = (concretise
    st).setLocal l (liftVal v)`. The bedrock for every per-event
    lemma that writes a local (move / copy / assign /
    mutBorrow_direct / endBorrow_direct / loopOwned). -/
theorem concretise_setLocal (st : SymState) (l : Nat)
    (v : AeneasCheck.LLBCSharp.Val) :
    concretise (st.setLocal l v) =
      (concretise st).setLocal l (liftVal v) := by
  unfold concretise SymState.setLocal LLBCState.setLocal
  congr 1
  exact liftEnv_insert st.env l v

/-- `addLoan` commute (conditional on freshness): if the new loan
    id `b` is at least the current `nextLoanId`, then
    `concretise (st.addLoan b inner kind) = (concretise st).bumpLoanId b`.
    The freshness premise mirrors `LStep`'s `loanIdFresh` premise;
    Phase C lemmas discharge it from the cert's id allocation
    monotonicity.

    The hashmap-fold equality
    `maxKeyPlusOne (loans.insert b _) = max (maxKeyPlusOne loans) (b+1)`
    is the load-bearing step. Sorry'd at M10.1e (last Phase B
    commit; G6 still exempt); Phase C closes when the first lemma
    that needs the equality fires (likely M10.2h
    `stepMutBorrow_direct_sound`). -/
theorem concretise_addLoan (st : SymState) (b : Nat)
    (inner : AeneasCheck.LLBCSharp.Val) (kind : LoanKind)
    (hFresh : maxKeyPlusOne st.loans ≤ b) :
    concretise (st.addLoan b inner kind) =
      (concretise st).bumpLoanId b := by
  unfold concretise SymState.addLoan LLBCState.bumpLoanId
  -- Both sides share `ctx`, `abs`, `freshness.nextAbsId`, `freshness.nextSymValId`.
  -- The only nontrivial obligation is on `freshness.nextLoanId`:
  --   maxKeyPlusOne (st.loans.insert b _) = max (maxKeyPlusOne st.loans) (b+1)
  -- which equals `b + 1` under `hFresh` (Nat.max_eq_right).
  refine LLBCState.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_⟩
  -- Remaining goal: equality of `freshness` (NonceCounters) records.
  -- The `nextAbsId` and `nextSymValId` fields are equal definitionally;
  -- only `nextLoanId` needs work.
  refine NonceCounters.mk.injEq .. |>.mpr ⟨?_, rfl, rfl⟩
  -- Goal: maxKeyPlusOne (st.loans.insert b _) = max (maxKeyPlusOne st.loans) (b + 1)
  rw [maxKeyPlusOne_insert_fresh _ _ _ hFresh]
  exact (Nat.max_eq_right (Nat.le_succ_of_le hFresh)).symm

/-- `takeLoan` commute: removing a loan from the replayer's loan
    store is a no-op on the paper side (loans live inside `ctx` /
    `abs`, not in a separate map). So if `takeLoan` returns `some
    (_, st')`, then `concretise st' = concretise st`. -/
theorem concretise_takeLoan (st : SymState) (b : Nat)
    {li : LoanInfo} {st' : SymState}
    (_hTake : st.takeLoan b = some (li, st')) :
    concretise st' = concretise st := by
  sorry

end AeneasSoundness.Soundness.Concretise
