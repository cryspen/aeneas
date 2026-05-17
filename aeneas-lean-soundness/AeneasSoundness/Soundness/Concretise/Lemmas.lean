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
open AeneasCheck.Raw (AbsShape)
open AeneasSoundness.LLBCSharpPaper (LLBCState NonceCounters liftAbsShape)

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
      { nextLoanId := st.loanIdHwm
        nextAbsId := st.absIdHwm
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

/-- `addLoan` commute (unconditional after M10.1g): `concretise`
    pushes through `addLoan` to the paper-side `bumpLoanId`.

    Why unconditional: `SymState.addLoan b _ _` updates `loanIdHwm`
    to `max st.loanIdHwm (b+1)`, and `concretise.freshness.nextLoanId
    := st.loanIdHwm`. The paper's `bumpLoanId b` does
    `nextLoanId := max nextLoanId (b+1)`. The two `max` expressions
    are syntactically identical; no freshness premise needed.
    Pre-M10.1g this lemma required `maxKeyPlusOne st.loans ≤ b`
    because `nextLoanId` derived from `maxKeyPlusOne loans`; with
    the HWM redesign that detour is gone. -/
theorem concretise_addLoan (st : SymState) (b : Nat)
    (inner : AeneasCheck.LLBCSharp.Val) (kind : LoanKind) :
    concretise (st.addLoan b inner kind) =
      (concretise st).bumpLoanId b := by
  unfold concretise SymState.addLoan LLBCState.bumpLoanId
  -- ctx, abs, freshness.nextAbsId, freshness.nextSymValId are all
  -- equal definitionally; only nextLoanId carries the `max` shape.
  refine LLBCState.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_⟩
  refine NonceCounters.mk.injEq .. |>.mpr ⟨rfl, rfl, rfl⟩

/-- `takeLoan` commute: removing a loan id from the replayer's
    loan store is a no-op on the paper side (loans live inside
    `ctx` / `abs`, not in a separate map; the monotone HWM
    `loanIdHwm` is untouched by `takeLoan`). So if `takeLoan b`
    returns `some (_, st')`, then `concretise st' = concretise st`. -/
theorem concretise_takeLoan (st : SymState) (b : Nat)
    {li : LoanInfo} {st' : SymState}
    (hTake : st.takeLoan b = some (li, st')) :
    concretise st' = concretise st := by
  unfold SymState.takeLoan at hTake
  split at hTake
  · cases hTake
  · rename_i li' hLook
    simp only [Option.some.injEq, Prod.mk.injEq] at hTake
    obtain ⟨_, hSt⟩ := hTake
    subst hSt
    unfold concretise
    -- ctx, abs, freshness all definitionally equal: loans.erase only
    -- changes st.loans (not env / absRegistry / loanIdHwm).
    rfl

/-! ## M10.1i (absRegistry mutators)

`addAbsShape` is the fold step `stepCall` uses to install each
`AbsShape` from the cert's `absSig`; `removeAbsShape` is what
`stepEndAbs` calls to drop the closing abstraction's registry
entry. Their paper-side mirrors:

* `addAbsShape` ↦ `setAbs shape.absId (liftAbsShape shape)` then
  `bumpAbsId shape.absId`. Unconditional (no freshness premise) —
  `absIdHwm` is the source of truth on both sides; the `max`
  expressions coincide by `rfl`.
* `removeAbsShape` ↦ `removeAbs absId`. Unconditional —
  `absIdHwm` is untouched on the replayer side, mirroring the
  paper's `LStep.endAbs` leaving freshness unchanged.

The pattern matches `concretise_addLoan` (post-M10.1g
unconditional) / `concretise_takeLoan`. -/

/-- `liftAbsRegistry (registry.insert k v)` is the function-update
    of `liftAbsRegistry registry` at `k` with `some (liftAbsShape
    v)`. Mirrors `liftEnv_insert`. -/
theorem liftAbsRegistry_insert (registry : Std.HashMap Nat AbsShape)
    (k : Nat) (shape : AbsShape) :
    liftAbsRegistry (registry.insert k shape) =
      Function.update (liftAbsRegistry registry) k (some (liftAbsShape shape)) := by
  funext k'
  unfold liftAbsRegistry
  by_cases h : k = k'
  · subst h; simp [Function.update]
  · simp [Std.HashMap.getElem?_insert, h, Function.update_of_ne (Ne.symm h)]

/-- `liftAbsRegistry (registry.erase k)` is the function-update of
    `liftAbsRegistry registry` at `k` with `none`. Mirror of
    `liftAbsRegistry_insert` for the erase path. -/
theorem liftAbsRegistry_erase (registry : Std.HashMap Nat AbsShape)
    (k : Nat) :
    liftAbsRegistry (registry.erase k) =
      Function.update (liftAbsRegistry registry) k none := by
  funext k'
  unfold liftAbsRegistry
  by_cases h : k = k'
  · subst h; simp [Function.update]
  · simp [Std.HashMap.getElem?_erase, h, Function.update_of_ne (Ne.symm h)]

/-- `addAbsShape` commute: installing one shape on the replayer side
    is `setAbs` then `bumpAbsId` on the paper side. Unconditional. -/
theorem concretise_addAbsShape (st : SymState) (shape : AbsShape) :
    concretise (st.addAbsShape shape) =
      ((concretise st).setAbs shape.absId (liftAbsShape shape)).bumpAbsId shape.absId := by
  unfold concretise SymState.addAbsShape LLBCState.setAbs LLBCState.bumpAbsId
  refine LLBCState.mk.injEq .. |>.mpr ⟨rfl, ?_, ?_⟩
  · exact liftAbsRegistry_insert st.absRegistry shape.absId shape
  · refine NonceCounters.mk.injEq .. |>.mpr ⟨rfl, rfl, rfl⟩

/-- `removeAbsShape` commute: erasing a registry entry on the
    replayer side is `removeAbs` on the paper side. Unconditional;
    `absIdHwm` is untouched on the replayer side, mirroring the
    paper's `LStep.endAbs` leaving freshness unchanged. -/
theorem concretise_removeAbsShape (st : SymState) (absId : Nat) :
    concretise (st.removeAbsShape absId) =
      (concretise st).removeAbs absId := by
  unfold concretise SymState.removeAbsShape LLBCState.removeAbs
  refine LLBCState.mk.injEq .. |>.mpr ⟨rfl, ?_, rfl⟩
  exact liftAbsRegistry_erase st.absRegistry absId

end AeneasSoundness.Soundness.Concretise
