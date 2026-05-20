import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.Soundness.StepEventSound

/-!
# Phase E — `replayFun` correspondence theorem

The trace-level lift of `stepEvent_sound`. Given a successful
`replayFun n f strictJoin = .ok trace`, we exhibit a paper-side
multi-step derivation `LStepStar` from the entry-state concretise
to the exit-state concretise, matching the cert's event list.

## What we prove

The headline theorem `replayFun_correspondence` states:

> If `replayFun n f strictJoin = .ok trace`, then
>   * `LStepStar (concretise (SymState.empty n)) trace.events.toList
>                (concretise trace.finalState)` —
>     a paper-side multi-step derivation from the empty entry state
>     to the replayer's final state, visiting each event in order.
>   * No `.direct` loan is live in `trace.finalState.loans` —
>     a structural exit condition the replayer enforces.

This is the *correspondence* statement: the cert is the trace of a
paper-side LLBC# execution. It does NOT claim:

* That the cert faithfully reflects the source Rust program. The
  OCaml-side `CertGen.ml` emitter is trusted to produce the cert;
  if the emitter has a bug (e.g. dropping borrow propagation
  events), the cert may be an incomplete picture of the actual
  execution. Our theorem still holds — the LStepStar derivation
  matches whatever events the cert emitted — but the gap from
  cert to source Rust is outside our scope.
* PL-level safety. The paper's safety theorem (Theorem 4.x)
  bridges `LStep*` to "Rust function is borrow-safe"; we do
  not axiomatize that theorem, so our library stops at the
  correspondence.

## What `Initial` and `Final` (Fig. 10) don't say here

The `LLBCSharpPaper.Initial` predicate from paper Fig. 10 requires
the entry state's input locals to be populated with symbolic
values. The replayer's `SymState.empty n` does NOT pre-populate
inputs — it lets the trace populate them via early `EvAssign`
events. As a result, `Initial (concretise (SymState.empty n)) sig
prog` is generally false for non-trivial signatures. We therefore
state the correspondence in terms of the entry concretise *as is*,
not via `Initial`.

The `Soundness.Final` predicate carries `concretise_matches`,
`no_direct_leak`, `return_populated`, and a placeholder for non-
direct leak tracking. The first two are direct corollaries of
`replayFun_correspondence`; `return_populated` requires inspection
of the cert's exit events (typically an `EvRetn` after the last
`EvAssign` to local 0) which is M11+ work.

## Proof structure

`replayFun n f` (M10.x.10c) desugars to:

```
let st ← f.events.foldlM (init := SymState.empty n)
  (replayFunStep f.fnId f.fnName strictJoin)
let leakedDirect := ...
if !leakedDirect.isEmpty then throw ... else return { ... finalState := st }
```

We prove a fold-form correspondence:

```
theorem foldlM_replayFunStep_correspondence
    {strictJoin : Bool} {fnId : Nat} {fnName : String}
    {events : List Event} {st st_n : SymState} {Ω : LLBCState}
    (hRep : concretise st = Ω) (hInv : LoanHwmInvariant st)
    (hFold : events.foldlM (replayFunStep fnId fnName strictJoin) st = .ok st_n) :
    LStepStar Ω events (concretise st_n) ∧ LoanHwmInvariant st_n
```

By induction on `events`. Nil: `LStepStar.nil`, invariant unchanged.
Cons: extract `replayFunStep` ⇒ `stepEvent`, apply `stepEvent_sound`
for the per-event paper-side step, apply
`loanHwm_preserved_stepEvent` for the invariant, recurse.

The `replayFun` wrapping (entry-state seeding + exit-leak check)
is then a post-processing wrapper.
-/

namespace AeneasSoundness.Soundness

open AeneasCheck.Raw AeneasCheck.LLBCSharp
open AeneasSoundness.LLBCSharpPaper (LLBCState LStep)
open AeneasSoundness.Soundness.Invariants (LoanHwmInvariant HwmInvariant)

/-! ## `LStepStar` — paper-side multi-step closure

A list-indexed inductive: `LStepStar Ω₀ events Ω_n` says there is
a chain `Ω₀ →_{e₁} Ω₁ →_{e₂} ⋯ →_{e_n} Ω_n` where each
`Ω_i →_{eᵢ} Ω_{i+1}` is an `LStep` derivation. The list is the
index so inversion gives both endpoints. -/
inductive LStepStar : LLBCState → List AeneasCheck.Raw.Event → LLBCState → Prop where
  /-- Empty chain: post = pre. -/
  | nil {Ω : LLBCState} : LStepStar Ω [] Ω
  /-- Step + recurse: `LStep Ω e Ω'`, then `LStepStar Ω' es Ω_n`. -/
  | cons {Ω Ω' Ω_n : LLBCState} {e : AeneasCheck.Raw.Event}
         {es : List AeneasCheck.Raw.Event} :
      LStep Ω e Ω' → LStepStar Ω' es Ω_n →
      LStepStar Ω (e :: es) Ω_n

/-! ## Inversion: `replayFunStep` ↔ `stepEvent`

The replayer's per-event wrapper just re-tags errors with a
function-context prefix; on the `.ok` side the underlying
`stepEvent` succeeds with the same post-state. -/

theorem replayFunStep_ok_iff_stepEvent_ok
    {strictJoin : Bool} {fnId : Nat} {fnName : String}
    {st st' : SymState} {ev : Event}
    (h : replayFunStep fnId fnName strictJoin st ev = .ok st') :
    stepEvent st ev strictJoin = .ok st' := by
  unfold replayFunStep at h
  split at h
  · rename_i st'' hStep
    simp only [Except.ok.injEq] at h
    subst h
    exact hStep
  · cases h

/-! ## Trace-level correspondence (fold form) -/

/-- Trace-level induction. From a successful `foldlM
    replayFunStep` on a list of events and matching invariants on
    the entry state, derive an `LStepStar` matching the events plus
    invariant preservation at the exit. -/
theorem foldlM_replayFunStep_correspondence
    {strictJoin : Bool} {fnId : Nat} {fnName : String} :
    ∀ (events : List Event) (st st_n : SymState) (Ω : LLBCState),
      concretise st = Ω →
      LoanHwmInvariant st →
      events.foldlM (replayFunStep fnId fnName strictJoin) st = .ok st_n →
      LStepStar Ω events (concretise st_n) ∧ LoanHwmInvariant st_n
  | [], st, st_n, _Ω, hRep, hInv, hFold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hFold
    subst hFold
    refine ⟨?_, hInv⟩
    rw [← hRep]
    exact LStepStar.nil
  | e :: rest, st, st_n, Ω, hRep, hInv, hFold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hFold
    cases hHead : replayFunStep fnId fnName strictJoin st e with
    | error _ => rw [hHead] at hFold; cases hFold
    | ok s1 =>
      rw [hHead] at hFold
      -- `replayFunStep` ok ⇒ `stepEvent` ok at the same post-state.
      have hStep : stepEvent st e strictJoin = .ok s1 :=
        replayFunStep_ok_iff_stepEvent_ok hHead
      -- Apply stepEvent_sound for the per-event LStep.
      obtain ⟨Ω', _hValid, hLStep, hConc⟩ :=
        stepEvent_sound e st s1 Ω hRep hInv hStep
      -- Maintain LoanHwmInvariant for the recursive call.
      have hInv1 : LoanHwmInvariant s1 :=
        Invariants.loanHwm_preserved_stepEvent hInv hStep
      -- Recurse on the tail.
      have hRest := foldlM_replayFunStep_correspondence rest s1 st_n Ω' hConc hInv1 hFold
      refine ⟨LStepStar.cons hLStep hRest.1, hRest.2⟩

/-! ## Headline theorem

`replayFun n f strictJoin = .ok trace` ⇒ existence of a paper-side
`LStepStar` derivation matching `trace.events`, plus no-direct-leak
at exit. -/

/-- M10.x.10c — `replayFun_correspondence`. Given a successful
    `replayFun n f`, exhibit:
    * a paper-side `LStepStar` derivation from the empty entry
      state's concretise to the replayer's exit state's concretise,
      visiting each event in `trace.events` in order, and
    * the no-direct-leak property at exit (every loan in
      `trace.finalState.loans` has non-`.direct` kind). -/
theorem replayFun_correspondence
    (numLocals : Nat) (f : FunCert) (strictJoin : Bool)
    (trace : CheckedTrace)
    (hReplay : replayFun numLocals f strictJoin = .ok trace) :
    LStepStar (Concretise.concretise (SymState.empty numLocals)) trace.events.toList
              (Concretise.concretise trace.finalState) ∧
    (∀ (b : Nat) (li : LoanInfo),
        trace.finalState.loans[b]? = some li → li.kind ≠ LoanKind.direct) := by
  unfold replayFun at hReplay
  -- Strip the do-block: first the foldlM, then the leaked-direct
  -- post-check, then the wrap into CheckedTrace.
  simp only [bind, Except.bind] at hReplay
  cases hFold : f.events.foldlM (init := SymState.empty numLocals)
                    (replayFunStep f.fnId f.fnName strictJoin) with
  | error _ => rw [hFold] at hReplay; cases hReplay
  | ok st_final =>
    rw [hFold] at hReplay
    simp only [] at hReplay
    -- Cases on whether `leakedDirect.isEmpty` is `true` or `false`.
    -- The replayer throws iff `!isEmpty = true`, i.e. non-empty.
    set leakedDirect :=
      (st_final.loans.toList.filterMap fun (b : Nat × LoanInfo) =>
        if b.2.kind == LoanKind.direct then some b.1 else none) with hLeakedDef
    by_cases hLeak : leakedDirect.isEmpty = true
    · -- Empty: replayer returns. Extract trace.
      simp only [hLeak, Bool.not_true, Bool.false_eq_true, if_false,
                 pure, Except.pure, Except.ok.injEq] at hReplay
      have hTraceEvents : trace.events = f.events := by rw [← hReplay]
      have hTraceFinal : trace.finalState = st_final := by rw [← hReplay]
      -- Convert foldlM over Array to foldlM over List.
      have hFoldList :
          f.events.toList.foldlM (replayFunStep f.fnId f.fnName strictJoin)
              (SymState.empty numLocals) = .ok st_final := by
        rw [← hFold]; simp [Array.foldlM_toList]
      have ⟨hChain, _hInvExit⟩ :=
        foldlM_replayFunStep_correspondence f.events.toList
          (SymState.empty numLocals) st_final
          (Concretise.concretise (SymState.empty numLocals))
          rfl (HwmInvariant.empty numLocals).toLoanHwm hFoldList
      refine ⟨?_, ?_⟩
      · rw [hTraceEvents, hTraceFinal]; exact hChain
      · rw [hTraceFinal]
        intro b li hb hKind
        have hPair : (b, li) ∈ st_final.loans.toList :=
          Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hb
        have hMem : b ∈ leakedDirect := by
          rw [hLeakedDef]
          rw [List.mem_filterMap]
          refine ⟨(b, li), hPair, ?_⟩
          rw [hKind]
          rw [show (LoanKind.direct == LoanKind.direct) = true from rfl]
          simp only [if_true]
        exact absurd (List.isEmpty_iff.mp hLeak) (List.ne_nil_of_mem hMem)
    · -- Non-empty: replayer throws. Contradiction with hReplay = .ok.
      have hNotEmpty : leakedDirect.isEmpty = false := by
        cases h : leakedDirect.isEmpty
        · rfl
        · exact absurd h hLeak
      simp only [hNotEmpty, Bool.not_false, if_true] at hReplay
      cases hReplay

end AeneasSoundness.Soundness
