import AeneasCheck.LLBCSharp.Step
import AeneasSoundness.LLBCSharpPaper.Step
import AeneasSoundness.Soundness.Concretise.Lemmas
import AeneasSoundness.Soundness.JoinLemmas

/-!
# M10.x.10 — `joinChainFoldStep` paper-side mirror + commute

The Path B replacement for `CertGen_faithful.join`. The replayer's
`stepJoin` now computes the chain's post-state by folding
`joinChainFoldStep` over the cert's `witnesses` array; this module
mirrors the same step on the paper side, proves the concretise
commute, and chains those into a `JoinChain` derivation that
witnesses `LStep.join`.

Three pieces:

1. `joinChainFoldStep_paper` — `Option`-flavored paper-side mirror
   of the replayer's `Result`-flavored chain step. The `some`/`none`
   distinction tracks the freshness / registry-existence premises
   each `JoinEntryStep` constructor needs.

2. `concretise_joinChainFoldStep` — per-step commute. From
   `joinChainFoldStep st entry = .ok st'` derive
   `joinChainFoldStep_paper (concretise st) entry = some (concretise st')`.
   Crucial: neither side bumps `loanIdHwm` / `absIdHwm` / `nextSymValId`
   in the step, so per-step freshness premises stay against the
   pre-fold state. This matches the M10.x.10 paper-rule revision
   (`JoinEntryStep.symbolic` drops `bumpSymValId`;
   `JoinEntryStep.mutBorrows` drops `bumpLoanId` and `bumpAbsId`).

3. `joinChain_of_paper_foldM` — given the paper-side fold output
   `some Ω'`, build a `JoinChain Ω witnesses Ω'`. Each chain link is
   one `JoinEntryStep` constructor applied with its premise.
-/

namespace AeneasSoundness.Soundness

open AeneasCheck.Raw AeneasCheck.LLBCSharp
open AeneasSoundness.LLBCSharpPaper (LLBCState liftAbsShape JoinEntryStep JoinChain)

private abbrev concretise : SymState → LLBCState := Concretise.concretise

/-- M10.x.10: paper-side mirror of the replayer's `joinChainFoldStep`.
    Cases on the cert rule, returning `none` when a freshness or
    registry-existence premise that the corresponding
    `JoinEntryStep` constructor needs is not satisfied; otherwise
    returning the chain step's post-state. -/
def joinChainFoldStep_paper (Ω : LLBCState) (entry : JoinEntry) :
    Option LLBCState :=
  match entry.rule with
  | .joinSame | .joinVar => some Ω
  | .joinSymbolic freshSv =>
    some (Ω.setLocal entry.localId (.sym freshSv))
  | .joinMutBorrows _ _ l_fresh absShape =>
    -- Use the raw `≤` form so Lean's `decide` finds the `Nat.decLe`
    -- instance; the `loanIdFresh` / `absIdFresh` abbreviations
    -- unfold to these.
    if Ω.freshness.nextLoanId ≤ l_fresh ∧ Ω.freshness.nextAbsId ≤ absShape.absId then
      some ((Ω.setLocal entry.localId (.mutBorrow l_fresh .bottom)).setAbs
              absShape.absId (liftAbsShape absShape))
    else none
  | .joinBottomOther absId | .joinOtherBottom absId =>
    match Ω.abs absId with
    | some _ => some Ω
    | none => none

/-- Helper: concretise commutes with `joinMutBorrowsStep`, yielding
    the paper-side `setLocal` + `setAbs` post-state. The two updates
    target distinct LLBCState fields (ctx vs abs) so they trivially
    commute on the paper side. -/
theorem concretise_joinMutBorrowsStep
    (st : SymState) (localId : Nat) (l_fresh : Nat) (absShape : AbsShape) :
    concretise (joinMutBorrowsStep st localId l_fresh absShape) =
      ((concretise st).setLocal localId
          (.mutBorrow l_fresh .bottom)).setAbs absShape.absId (liftAbsShape absShape) := by
  unfold joinMutBorrowsStep concretise Concretise.concretise
    LLBCSharpPaper.LLBCState.setLocal LLBCSharpPaper.LLBCState.setAbs
    SymState.setLocal
  -- After unfolds, both sides have the same struct skeleton; ctx and abs
  -- updates pointwise reduce by funext + per-key case-split.
  refine LLBCSharpPaper.LLBCState.mk.injEq .. |>.mpr ⟨?_, ?_, rfl⟩
  · -- ctx field: liftEnv (env.insert _ _) = Function.update (liftEnv env) _ _.
    exact Concretise.liftEnv_insert _ _ _
  · -- abs field: liftAbsRegistry (registry.insert _ _) = Function.update _ _ _.
    exact Concretise.liftAbsRegistry_insert _ _ _

/-! ### Per-step commute -/

/-- `concretise` commutes with the replayer's `joinChainFoldStep`:
    every `.ok` step on the replayer side maps to a `some` step on
    the paper side at the same post-state.

    Case-by-case the cert rule. The non-trivial arms:

    * `joinSymbolic`: replayer does `setLocal _ (.sym freshSv)`;
      paper-side does the same. Discharge by `concretise_setLocal`
      and `liftVal (.sym freshSv) = .sym freshSv`.
    * `joinMutBorrows`: replayer does `joinMutBorrowsStep` (a
      `setLocal` of `.mutBorrow l_fresh .bottom` plus an
      `absRegistry.insert` of `absShape`). Paper-side mirror is
      `setLocal _ (.mutBorrow l_fresh .bottom)` then
      `setAbs absShape.absId (liftAbsShape absShape)`. Discharge
      by `concretise_setLocal` and the `Function.update`-as-
      `setAbs` form from `liftAbsRegistry_insert`. The replayer
      fails when `l_fresh < st.loanIdHwm` or
      `absShape.absId < st.absIdHwm`; both `not_lt`-flip to give
      paper-side `loanIdFresh` / `absIdFresh` premises.
    * `joinBottomOther` / `joinOtherBottom`: replayer fails when
      the abs id is not in `st.absRegistry`; paper-side requires
      the abs to be in `Ω.abs`. `concretise_abs_apply` ties the
      two: `(concretise st).abs absId = some _` iff
      `st.absRegistry.contains absId = true`. -/
theorem concretise_joinChainFoldStep
    (st : SymState) (entry : JoinEntry) (st' : SymState)
    (hStep : joinChainFoldStep st entry = .ok st') :
    joinChainFoldStep_paper (concretise st) entry = some (concretise st') := by
  unfold joinChainFoldStep at hStep
  unfold joinChainFoldStep_paper
  -- Case-split on the rule. After each `rw [hRule]`, do `simp only []`
  -- to trigger iota reduction on the now-known constructor scrutinee
  -- (the M10.x.9 pattern from `stepEndBorrow_*` proofs).
  cases hRule : entry.rule with
  | joinSame =>
    rw [hRule] at hStep
    simp only [] at hStep ⊢
    simp only [pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    rfl
  | joinVar =>
    rw [hRule] at hStep
    simp only [] at hStep ⊢
    simp only [pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    rfl
  | joinSymbolic freshSv =>
    rw [hRule] at hStep
    simp only [] at hStep ⊢
    simp only [pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    -- Goal: some ((concretise st).setLocal _ (.sym freshSv)) =
    --       some (concretise (st.setLocal _ (.sym freshSv)))
    -- The `concretise` abbrev needs to be folded back so the commute
    -- lemma's pattern matches.
    show some ((Concretise.concretise st).setLocal entry.localId (.sym freshSv)) =
         some (Concretise.concretise (st.setLocal entry.localId (.sym freshSv)))
    rw [Concretise.concretise_setLocal]
    rfl
  | joinMutBorrows l_left l_right l_fresh absShape =>
    rw [hRule] at hStep
    simp only [] at hStep ⊢
    by_cases h1 : l_fresh < st.loanIdHwm
    · simp only [h1, if_true] at hStep
      cases hStep
    · simp only [h1, if_false] at hStep
      by_cases h2 : absShape.absId < st.absIdHwm
      · simp only [h2, if_true] at hStep
        cases hStep
      · simp only [h2, if_false, pure, Except.pure, Except.ok.injEq] at hStep
        subst hStep
        have hLF : (concretise st).freshness.nextLoanId ≤ l_fresh := by
          rw [Concretise.concretise_freshness]
          exact Nat.not_lt.mp h1
        have hAF : (concretise st).freshness.nextAbsId ≤ absShape.absId := by
          rw [Concretise.concretise_freshness]
          exact Nat.not_lt.mp h2
        rw [if_pos ⟨hLF, hAF⟩]
        -- Goal: some ((concretise st).setLocal _ (.mutBorrow l_fresh .bottom)).setAbs _ _
        --     = some (concretise (joinMutBorrowsStep ...))
        rw [concretise_joinMutBorrowsStep]
  | joinBottomOther absId =>
    rw [hRule] at hStep
    simp only [] at hStep ⊢
    by_cases hC : st.absRegistry.contains absId = true
    · -- contains = true: replayer's `!contains` is false → else branch → ok st.
      rw [hC] at hStep
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
                 pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      have hSome : (st.absRegistry[absId]?).isSome :=
        Std.HashMap.isSome_getElem?_iff_mem.mpr hC
      rcases hLook : st.absRegistry[absId]? with _ | shape
      · rw [hLook] at hSome; cases hSome
      · have hAbs : (concretise st).abs absId = some (liftAbsShape shape) := by
          rw [Concretise.concretise_abs_apply, hLook]; rfl
        rw [hAbs]
    · have hCF : st.absRegistry.contains absId = false := by
        cases hCC : st.absRegistry.contains absId
        · rfl
        · exact absurd hCC hC
      rw [hCF] at hStep
      simp only [Bool.not_false, if_true, pure, Except.pure] at hStep
      cases hStep
  | joinOtherBottom absId =>
    rw [hRule] at hStep
    simp only [] at hStep ⊢
    by_cases hC : st.absRegistry.contains absId = true
    · rw [hC] at hStep
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
                 pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      have hSome : (st.absRegistry[absId]?).isSome :=
        Std.HashMap.isSome_getElem?_iff_mem.mpr hC
      rcases hLook : st.absRegistry[absId]? with _ | shape
      · rw [hLook] at hSome; cases hSome
      · have hAbs : (concretise st).abs absId = some (liftAbsShape shape) := by
          rw [Concretise.concretise_abs_apply, hLook]; rfl
        rw [hAbs]
    · have hCF : st.absRegistry.contains absId = false := by
        cases hCC : st.absRegistry.contains absId
        · rfl
        · exact absurd hCC hC
      rw [hCF] at hStep
      simp only [Bool.not_false, if_true, pure, Except.pure] at hStep
      cases hStep

/-! ### Fold-style commute (over a `List`)

The replayer uses `Array.foldlM`; the paper-side fold is via
`List.foldlM` on `witnesses.toList`. `Array.foldlM` collapses to
its `toList.foldlM` form by a simp lemma.
-/

private theorem concretise_foldlM_joinChainFoldStep_aux
    : ∀ (xs : List JoinEntry) (st st' : SymState),
        xs.foldlM joinChainFoldStep st = .ok st' →
        xs.foldlM joinChainFoldStep_paper (concretise st) = some (concretise st')
  | [], st, st', hStep => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hStep
    simp only [List.foldlM_nil, pure]
    rw [hStep]
  | e :: rest, st, st', hStep => by
    simp only [List.foldlM_cons, bind, Except.bind] at hStep
    -- hStep matches on `joinChainFoldStep st e`; the .error case kills hStep.
    cases hHead : joinChainFoldStep st e with
    | error _ =>
      rw [hHead] at hStep
      cases hStep
    | ok st1 =>
      rw [hHead] at hStep
      have hPaperHead := concretise_joinChainFoldStep st e st1 hHead
      have hIH := concretise_foldlM_joinChainFoldStep_aux rest st1 st' hStep
      simp only [List.foldlM_cons, bind, Option.bind, hPaperHead]
      exact hIH

theorem concretise_foldlM_joinChainFoldStep
    (xs : List JoinEntry) (st st' : SymState)
    (hStep : xs.foldlM joinChainFoldStep st = .ok st') :
    xs.foldlM joinChainFoldStep_paper (concretise st) = some (concretise st') :=
  concretise_foldlM_joinChainFoldStep_aux xs st st' hStep

/-! ### Chain construction from paper-side fold output -/

/-- From the paper-side `foldlM joinChainFoldStep_paper Ω = some Ω'`,
    build a `JoinChain Ω xs Ω'`. Each chain link applies the
    matching `JoinEntryStep` constructor with the freshness /
    registry-existence premise extracted from the per-step `some`. -/
theorem joinChain_of_paper_foldM
    : ∀ (xs : List JoinEntry) (Ω Ω' : LLBCState),
        xs.foldlM joinChainFoldStep_paper Ω = some Ω' →
        JoinChain Ω xs Ω'
  | [], Ω, Ω', hFold => by
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hFold
    subst hFold
    exact JoinChain.nil
  | e :: rest, Ω, Ω', hFold => by
    simp only [List.foldlM_cons, bind, Option.bind] at hFold
    -- Destructure: joinChainFoldStep_paper Ω e = some Ω1, recurse for rest.
    cases hHead : joinChainFoldStep_paper Ω e with
    | none =>
      rw [hHead] at hFold
      cases hFold
    | some Ω1 =>
      rw [hHead] at hFold
      -- hFold: rest.foldlM joinChainFoldStep_paper Ω1 = some Ω'
      have hTail := joinChain_of_paper_foldM rest Ω1 Ω' hFold
      -- Now build JoinEntryStep Ω e Ω1 from hHead.
      have hHeadStep : JoinEntryStep Ω e Ω1 := by
        unfold joinChainFoldStep_paper at hHead
        cases hRule : e.rule with
        | joinSame =>
          rw [hRule] at hHead
          simp only [] at hHead
          simp only [Option.some.injEq] at hHead
          subst hHead
          have : e = ⟨e.localId, .joinSame, e.delta⟩ := by
            cases e; rename_i lid r d
            simp at hRule
            subst hRule
            rfl
          rw [this]
          exact JoinEntryStep.same
        | joinVar =>
          rw [hRule] at hHead
          simp only [] at hHead
          simp only [Option.some.injEq] at hHead
          subst hHead
          have : e = ⟨e.localId, .joinVar, e.delta⟩ := by
            cases e; rename_i lid r d
            simp at hRule
            subst hRule
            rfl
          rw [this]
          exact JoinEntryStep.var
        | joinSymbolic freshSv =>
          rw [hRule] at hHead
          simp only [] at hHead
          simp only [Option.some.injEq] at hHead
          subst hHead
          have : e = ⟨e.localId, .joinSymbolic freshSv, e.delta⟩ := by
            cases e; rename_i lid r d
            simp at hRule
            subst hRule
            rfl
          rw [this]
          exact JoinEntryStep.symbolic
        | joinMutBorrows l_left l_right l_fresh absShape =>
          rw [hRule] at hHead
          simp only [] at hHead
          by_cases hPre : Ω.freshness.nextLoanId ≤ l_fresh ∧
                          Ω.freshness.nextAbsId ≤ absShape.absId
          · rw [if_pos hPre] at hHead
            simp only [Option.some.injEq] at hHead
            subst hHead
            obtain ⟨hLF, hAF⟩ := hPre
            have : e = ⟨e.localId, .joinMutBorrows l_left l_right l_fresh absShape, e.delta⟩ := by
              cases e; rename_i lid r d
              simp at hRule
              subst hRule
              rfl
            rw [this]
            exact JoinEntryStep.mutBorrows hLF hAF
          · rw [if_neg hPre] at hHead
            cases hHead
        | joinBottomOther absId =>
          rw [hRule] at hHead
          simp only [] at hHead
          cases hAbs : Ω.abs absId with
          | none =>
            rw [hAbs] at hHead
            simp only [] at hHead
            cases hHead
          | some r =>
            rw [hAbs] at hHead
            simp only [] at hHead
            simp only [Option.some.injEq] at hHead
            subst hHead
            have : e = ⟨e.localId, .joinBottomOther absId, e.delta⟩ := by
              cases e; rename_i lid rule d
              simp at hRule
              subst hRule
              rfl
            rw [this]
            exact JoinEntryStep.bottomOther hAbs
        | joinOtherBottom absId =>
          rw [hRule] at hHead
          simp only [] at hHead
          cases hAbs : Ω.abs absId with
          | none =>
            rw [hAbs] at hHead
            simp only [] at hHead
            cases hHead
          | some r =>
            rw [hAbs] at hHead
            simp only [] at hHead
            simp only [Option.some.injEq] at hHead
            subst hHead
            have : e = ⟨e.localId, .joinOtherBottom absId, e.delta⟩ := by
              cases e; rename_i lid rule d
              simp at hRule
              subst hRule
              rfl
            rw [this]
            exact JoinEntryStep.otherBottom hAbs
      exact JoinChain.cons hHeadStep hTail

/-! ### `stepJoin` soundness via the chain-fold

M10.x.10: replaces the `CertGen_faithful.join` axiom. Inverting
`hStep` through `stepJoinBody` yields the chain-fold output;
`concretise_foldlM_joinChainFoldStep` lifts that to a paper-side
fold; `joinChain_of_paper_foldM` builds the `JoinChain`; `LStep.join`
wraps it. -/

/-- Inversion: `stepJoinBody` (M10.x.10b) is the chain fold. Its
    `.ok` result IS the chain-fold output — no post-processing,
    no `loans` overwrite. -/
theorem stepJoinBody_chain_extract
    (st st' : SymState) (result : StateSummary) (witnesses : Array JoinEntry)
    (hStep : stepJoinBody st result witnesses = .ok st') :
    witnesses.foldlM joinChainFoldStep st = .ok st' := by
  unfold stepJoinBody at hStep
  exact hStep

end AeneasSoundness.Soundness
