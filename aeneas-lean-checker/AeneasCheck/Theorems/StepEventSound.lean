import AeneasCheck.LLBCSharp.Replay

/-!
# Soundness of `stepEvent` (skeleton)

This file is the M9.6 (Option C) Phase-6 deliverable from
`documentation/option-c-implementation-plan.md` §6 and plan §7.1
commit #24. It lays out the per-event case-analysis structure
the soundness proof will use — every event constructor maps to
one (or, with a hint, one-of-N) paper rule, and the M9.6
hint fields drive the case discrimination.

**No proofs are filled in.** The theorem statement is
parameterised over yet-to-be-defined sorts (`LLBCState`,
`⟦·⟧`, `LStep`, `Valid`) so the skeleton compiles against the
existing replayer. The real proof lands as part of the M10
"port LLBC# semantics to Lean" roadmap; see
`cert-format-and-soundness.md` §5 for the planned ordering.

The structure deliberately mirrors plan §6.3:
```
theorem stepEvent_sound :
  ∀ ev st st' Ω, ⟦st⟧ = Ω → stepEvent st ev = .ok st' →
    ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ ⟦st'⟧ = Ω'
```
The hint-bearing events sub-case on the hint constructor; the
non-hinted events case directly on the constructor.
-/

namespace AeneasCheck.Theorems

open AeneasCheck.Raw AeneasCheck.LLBCSharp

/-! ## Abstract paper-side surface

These four sorts are the load-bearing pieces of the LLBC#
semantics (per paper §4.1 + §5 figures). M9.6 leaves them
axiom so the skeleton typechecks; the real Lean port lives in
a future `AeneasCheck.LLBCSharpPaper` module.
-/

/-- The paper's `Ω#` LLBC# state — a value-grammar context
    plus a region-abstraction grammar `A_in(ρ) { borrow^m ℓ _,
    loan^m ℓ' }`. M9.6 stubs it as an axiom type. -/
axiom LLBCState : Type

/-- Concretisation function: lift the replayer's restricted
    [SymState] into a full LLBC# state by materialising trivial
    region abstractions for each `.reborrow` / `.lazyExpand`
    loan and consulting [SymState.absRegistry] for the real
    `A_in(ρ)` content of caller abstractions. -/
axiom concretise : SymState → LLBCState

/-- Per-event LLBC# side-conditions (paper Fig. 3 / 9 / 11).
    Each constructor's `Valid` payload is the conjunction of
    the rule's premises. -/
axiom Valid : Event → LLBCState → Prop

/-- One-step LLBC# reduction `Ω ⟶_# Ω'` witnessed by the
    event. For hinted events (EvMutBorrow, EvJoin, …) the
    reduction's rule choice is determined by the hint. -/
axiom LStep : LLBCState → Event → LLBCState → Prop

/-! ## Per-event sub-soundness lemmas (all stubbed)

Each lemma corresponds to one paper rule. The hint-bearing
events split into N lemmas (one per hint constructor); the
non-hinted events have a single lemma.
-/

section StepEvent

variable (st st' : SymState) (Ω : LLBCState)
variable (hRep : concretise st = Ω)

/-- M9.6 hint case: `EvMutBorrow { kind_hint = MbkDirect }`
    triggers `E-MutBorrow` (paper Fig. 3). -/
axiom stepMutBorrow_direct_sound
  (loan : Nat) (place : Place) (symval : Nat) :
  stepEvent st (.mutBorrow loan place symval .direct) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval .direct) Ω ∧
        LStep Ω (.mutBorrow loan place symval .direct) Ω' ∧
        concretise st' = Ω'

/-- M9.6 hint case: `kind_hint = MbkInAbsReborrow abs` triggers
    `Le-Reborrow-MutBorrow-Abs` (paper Fig. 8) on the named abs. -/
axiom stepMutBorrow_inAbsReborrow_sound
  (loan : Nat) (place : Place) (symval : Nat) (absId : Nat) :
  stepEvent st
    (.mutBorrow loan place symval (.inAbsReborrow absId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω' ∧
        concretise st' = Ω'

/-- M9.6 hint case: `kind_hint = MbkLoopOwned loop` triggers the
    loop-fixpoint borrow rule (paper §5.2). -/
axiom stepMutBorrow_loopOwned_sound
  (loan : Nat) (place : Place) (symval : Nat) (loopId : Nat) :
  stepEvent st
    (.mutBorrow loan place symval (.loopOwned loopId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.loopOwned loopId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.loopOwned loopId)) Ω' ∧
        concretise st' = Ω'

/-- `EvJoin { witnesses }` triggers the conjunction of the
    Fig. 11 rules named by each witness. Per-entry induction
    over [witnesses] is the heart of the join soundness proof. -/
axiom stepJoin_witnessed_sound
  (left right result : StateSummary) (witnesses : Array JoinEntry) :
  stepEvent st (.join left right result witnesses) = .ok st' →
  ∃ Ω', Valid (.join left right result witnesses) Ω ∧
        LStep Ω (.join left right result witnesses) Ω' ∧
        concretise st' = Ω'

end StepEvent

/-! ## Top-level: stepEvent_sound

Case-analysis on `ev`. Hint-bearing events sub-case on the
hint and delegate to the per-rule lemma above; non-hinted
events apply their single-rule lemma directly.
-/

axiom stepEvent_sound :
    ∀ (ev : Event) (st st' : SymState) (Ω : LLBCState),
      concretise st = Ω →
      stepEvent st ev = .ok st' →
      ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ concretise st' = Ω'

/-! ## Cross-cutting consequences (sketched in
`cert-format-and-soundness.md` §4.3 / §4.4)

* `replayFun_sound` — induction on the events array, threading
  the per-event lemma through.
* `replayCrate_implies_borrow_checks` — quantify
  `replayFun_sound` over `cc.functions`.

Both will move into this namespace once the LLBCState port
lands. Until then, this file is a documentation artifact:
the `axiom` placeholders make it clear that the M9.6 hint
schema is *sufficient* for the proof structure (every event
either has a unique rule or carries a hint that names the
rule) without yet committing to a specific Lean realisation
of the LLBC# semantics.
-/

end AeneasCheck.Theorems
