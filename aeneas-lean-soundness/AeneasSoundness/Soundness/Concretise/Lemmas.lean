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
open AeneasSoundness.LLBCSharpPaper (LLBCState)

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

end AeneasSoundness.Soundness.Concretise
