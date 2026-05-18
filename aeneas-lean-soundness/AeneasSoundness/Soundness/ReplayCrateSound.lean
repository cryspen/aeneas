import AeneasSoundness.Soundness.ReplayFunSound

/-!
# Phase F — `replayCrate` correspondence theorem

The crate-level lift of `replayFun_correspondence`. Given a
successful `replayCrate cc strictJoin = .ok results`, each function
in `cc.functions` has a matching trace in `results` such that the
per-function `LStepStar` correspondence and no-direct-leak property
hold.

## What we prove

```
theorem replayCrate_correspondence
    (cc : CrateCert) (strictJoin : Bool) (results : Array CheckedTrace)
    (hReplay : replayCrate cc strictJoin = .ok results) :
    results.size = cc.functions.size ∧
    ∀ (i : Nat) (hi : i < results.size),
      LStepStar
        (Concretise.concretise (SymState.empty results[i].finalState.numLocals))
        results[i].events.toList
        (Concretise.concretise results[i].finalState) ∧
      (∀ b li, results[i].finalState.loans[b]? = some li → li.kind ≠ LoanKind.direct)
```

This is the crate-level mechanized correspondence. Per-index, each
trace in `results` is the trace of a paper-side LLBC# execution
matching the function's events. Same trust-boundary caveats as
Phase E: no cert-faithfulness claim, no PL-safety claim.

## Proof structure

`replayCrate` (M10.x.10d) desugars to:

```
do
  let _ ← AeneasCheck.Typecheck.Consistency.checkLlbcVsCert cc  -- consistency
  let _ ← AeneasCheck.Typecheck.checkCrateCert cc                -- structural
  cc.functions.foldlM (init := #[]) fun acc f => do
    let trace ← replayCrateStep strictJoin f
    return acc.push trace
```

Two typecheck failures yield `.error`; on `.ok results`, the foldlM
succeeded. We invert the fold to extract per-function
`replayCrateStep strictJoin f = .ok trace` for each `f`, apply
`replayFun_correspondence` per-function, and package.

The per-function `replayCrateStep` is just
`replayFun (inferNumLocals f.events) f strictJoin`, so unwrapping
gives us the input shape `replayFun_correspondence` expects.
-/

namespace AeneasSoundness.Soundness

open AeneasCheck.Raw AeneasCheck.LLBCSharp AeneasCheck.Typecheck
open AeneasSoundness.LLBCSharpPaper (LLBCState LStep)

/-! ## Fold-form correspondence

The trace-accumulating foldlM `replayCrate` uses produces an array
of `CheckedTrace`s. We characterise its success: each step
succeeds and the running accumulator grows by `.push`. -/

private theorem foldlM_replayCrateStep_index_correspondence
    {strictJoin : Bool} :
    ∀ (fs : List FunCert) (init out : Array CheckedTrace),
      fs.foldlM (fun acc f => do
                  let trace ← replayCrateStep strictJoin f
                  return acc.push trace) init = .ok out →
      out.size = init.size + fs.length ∧
      (∀ (i : Nat) (h_in : i < init.size), ∃ (hi : i < out.size), out[i] = init[i]) ∧
      (∀ (j : Nat) (hj : j < fs.length),
        ∃ (hi : init.size + j < out.size),
          replayCrateStep strictJoin fs[j] = .ok out[init.size + j])
  | [], init, out, hFold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hFold
    subst hFold
    refine ⟨?_, ?_, ?_⟩
    · simp
    · intro i hi
      refine ⟨hi, rfl⟩
    · intro j hj
      exact absurd hj (Nat.not_lt_zero _)
  | f :: rest, init, out, hFold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hFold
    cases hStep : replayCrateStep strictJoin f with
    | error _ => rw [hStep] at hFold; cases hFold
    | ok trace =>
      rw [hStep] at hFold
      simp only [pure, Except.pure] at hFold
      have ih := foldlM_replayCrateStep_index_correspondence rest (init.push trace) out hFold
      obtain ⟨hSize, hOld, hNew⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · -- Size: out.size = (init.push trace).size + rest.length
        --                = init.size + 1 + rest.length
        --                = init.size + (rest.length + 1)
        rw [hSize]; simp [Array.size_push]; omega
      · -- Old indices: i < init.size → i < init.push trace .size → use hOld + Array.getElem_push.
        intro i hi
        have hi' : i < (init.push trace).size := by simp [Array.size_push]; omega
        obtain ⟨hir, hEq⟩ := hOld i hi'
        refine ⟨hir, ?_⟩
        rw [hEq]
        -- (init.push trace)[i] = init[i] when i < init.size.
        simp [Array.getElem_push, hi]
      · -- New indices: j < (f :: rest).length.
        -- If j = 0: corresponds to `trace` at position init.size of out.
        -- If j > 0: corresponds to rest[j-1] at position init.size + j of out.
        intro j hj
        match j with
        | 0 =>
          -- j = 0: f is the head; init.size + 0 = init.size is where `trace` landed.
          have hi : init.size + 0 < out.size := by
            rw [hSize]; simp [Array.size_push, List.length_cons]; omega
          refine ⟨hi, ?_⟩
          -- Get from hOld at position init.size:
          have hpush : init.size < (init.push trace).size := by
            simp [Array.size_push]
          obtain ⟨hir, hEq⟩ := hOld init.size hpush
          show replayCrateStep strictJoin (f :: rest)[0] = .ok out[init.size + 0]
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [hEq]
          -- (init.push trace)[init.size] = trace.
          simp [Array.getElem_push]
          exact hStep
        | Nat.succ j' =>
          have hj' : j' < rest.length := by
            simp [List.length_cons] at hj; omega
          obtain ⟨hi, hStepRest⟩ := hNew j' hj'
          have hi' : init.size + (j' + 1) < out.size := by
            have := hi; simp [Array.size_push] at this; omega
          refine ⟨hi', ?_⟩
          -- After Array index rewriting: (init.push trace).size + j' = init.size + (j' + 1).
          have hIdxEq : (init.push trace).size + j' = init.size + (j' + 1) := by
            simp [Array.size_push]; omega
          have hLhsCons : (f :: rest)[j' + 1] = rest[j'] := by
            simp [List.getElem_cons_succ]
          -- Goal: replayCrateStep _ (f :: rest)[j' + 1] = .ok out[init.size + (j' + 1)]
          rw [hLhsCons]
          -- Goal: replayCrateStep _ rest[j'] = .ok out[init.size + (j' + 1)]
          -- hStepRest : replayCrateStep _ rest[j'] = .ok out[(init.push trace).size + j']
          -- Use Eq.mp / Array.getElem_congr to swap index.
          have hOutEq : out[(init.push trace).size + j']'hi = out[init.size + (j' + 1)]'hi' := by
            congr 1
          rw [← hOutEq]
          exact hStepRest

/-! ## Headline theorem -/

/-- M10.x.10d — `replayCrate_correspondence`. The crate-level
    correspondence: every function in `cc.functions` has a matching
    `CheckedTrace` in `results` at the same index, and each trace
    satisfies the per-function `replayFun_correspondence`. The
    entry-state `numLocals` is `AeneasCheck.Typecheck.inferNumLocals f.events`
    (mirroring `replayFun`'s seed). -/
theorem replayCrate_correspondence
    (cc : CrateCert) (strictJoin : Bool) (results : Array CheckedTrace)
    (hReplay : replayCrate cc strictJoin = .ok results) :
    results.size = cc.functions.size ∧
    ∀ (i : Nat) (hi : i < cc.functions.size),
      ∃ (hir : i < results.size),
        LStepStar
          (Concretise.concretise
              (SymState.empty (AeneasCheck.Typecheck.inferNumLocals cc.functions[i].events)))
          results[i].events.toList
          (Concretise.concretise results[i].finalState) ∧
        (∀ (b : Nat) (li : LoanInfo),
            results[i].finalState.loans[b]? = some li → li.kind ≠ LoanKind.direct) := by
  -- Unfold replayCrate. Two typecheck guards, then the fold.
  unfold replayCrate at hReplay
  simp only [bind, Except.bind] at hReplay
  -- Strip both typecheck guards by cases.
  cases hCons : AeneasCheck.Typecheck.Consistency.checkLlbcVsCert cc with
  | error _ => rw [hCons] at hReplay; cases hReplay
  | ok _ =>
    rw [hCons] at hReplay
    simp only [] at hReplay
    cases hTC : AeneasCheck.Typecheck.checkCrateCert cc with
    | error _ => rw [hTC] at hReplay; cases hReplay
    | ok _ =>
      rw [hTC] at hReplay
      simp only [] at hReplay
      -- Convert Array.foldlM to List.foldlM.
      have hFoldList :
          cc.functions.toList.foldlM (fun acc f => do
              let trace ← replayCrateStep strictJoin f
              return acc.push trace) #[] = .ok results := by
        rw [← Array.foldlM_toList] at hReplay
        exact hReplay
      obtain ⟨hSize, _hOld, hNew⟩ :=
        foldlM_replayCrateStep_index_correspondence cc.functions.toList
          #[] results hFoldList
      have hSizeEq : results.size = cc.functions.size := by
        rw [hSize]; simp
      refine ⟨hSizeEq, ?_⟩
      intro i hi
      have hir : i < results.size := by rw [hSizeEq]; exact hi
      refine ⟨hir, ?_⟩
      have hi' : i < cc.functions.toList.length := by
        rw [Array.length_toList]; exact hi
      obtain ⟨hirRaw, hStep⟩ := hNew i hi'
      unfold replayCrateStep at hStep
      have hFunIdx : cc.functions.toList[i] = cc.functions[i] := by
        simp [Array.getElem_toList]
      rw [hFunIdx] at hStep
      -- hStep : replayFun ... = .ok results[#[].size + i]'hirRaw.
      -- Align the result index #[].size + i = i (Array.size_empty + Nat.zero_add).
      have hZeroAdd : (#[] : Array CheckedTrace).size + i = i := by simp
      have hResIdx : results[(#[] : Array CheckedTrace).size + i]'hirRaw =
                     results[i]'hir := by
        congr 1 <;> exact hZeroAdd
      rw [hResIdx] at hStep
      exact replayFun_correspondence
        (AeneasCheck.Typecheck.inferNumLocals cc.functions[i].events)
        cc.functions[i] strictJoin results[i] hStep

end AeneasSoundness.Soundness
