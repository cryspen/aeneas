import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.LLBCSharpPaper.Step
import AeneasSoundness.LLBCSharpPaper.Valid

/-!
# Soundness of `stepEvent`

This file is the M10 Phase-A vertical-slice anchor. After M10.0a–j
moved the four `axiom` stubs (`LLBCState`, `concretise`, `Valid`,
`LStep`) into a fully Lean-ported paper-side surface
(`AeneasSoundness.LLBCSharpPaper.*`), M10.0k now replaces those
axioms with imports of the real defs and turns every per-event
`axiom` into a `theorem … := by sorry`. The `sorry`s land *inside*
`Soundness/`; G6 is *exempted* for Phase A per plan §10.1 (G6 runs
from Phase C onward; commits #17+).

Concretely:

* `LLBCState` is now the structure from
  `LLBCSharpPaper/State.lean`.
* `LStep` is the inductive relation from `LLBCSharpPaper/Step.lean`
  (27 constructors).
* `Valid` is the `match`-on-`Event` predicate from
  `LLBCSharpPaper/Valid.lean`.
* `concretise` is *still* a placeholder — a `def` that always
  returns `LLBCState.empty`. The real concretisation lands at
  M10.1a/b (Phase B); the placeholder is what makes the M10.0k
  axiom inventory clean.

After M10.0k, the per-event lemmas and the top-level
`stepEvent_sound` are `theorem`s witnessed by `sorry`; Phase B–D
discharge them. `#print axioms stepEvent_sound` reports
`sorryAx` (plus `propext` / `Quot.sound` from core) and nothing
else.

The structure deliberately mirrors plan §6.3:
```
theorem stepEvent_sound :
  ∀ ev st st' Ω, ⟦st⟧ = Ω → stepEvent st ev = .ok st' →
    ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ ⟦st'⟧ = Ω'
```
The hint-bearing events sub-case on the hint constructor; the
non-hinted events case directly on the constructor.
-/

namespace AeneasSoundness.Soundness

open AeneasCheck.Raw AeneasCheck.LLBCSharp
open AeneasSoundness.LLBCSharpPaper (LLBCState LStep Valid)

/-! ## Concretisation (placeholder)

M10.0k keeps `concretise` as a `def` returning the empty
`LLBCState` so the file typechecks against real types. The real
definition lands in `Concretise/Defn.lean` at M10.1a-b (Phase B);
M10.1d-e prove its commute lemmas, which Phase C consumes to
discharge each per-event sorry. -/

/-- Placeholder concretisation. Returns the empty `LLBCState` for
    every `SymState`. The Phase-B replacement
    (`Concretise/Defn.lean`) is faithful: it lifts the SymState's
    env / loans / absRegistry into the paper-side `LLBCState` per
    plan §2.1. The placeholder is sound-by-vacuous-premise: every
    per-event lemma below is `sorry`'d, so no proof presently
    depends on `concretise`'s shape. -/
def concretise (_ : SymState) : LLBCState := LLBCState.empty

/-! ## Per-event sub-soundness lemmas (all `sorry`'d) -/

section StepEvent

variable (st st' : SymState) (Ω : LLBCState)
variable (hRep : concretise st = Ω)

/-- M9.6 hint case: `EvMutBorrow { kind_hint = MbkDirect }` triggers
    `E-MutBorrow` (paper Fig. 3). Closed by Phase-C M10.2h. -/
theorem stepMutBorrow_direct_sound
  (loan : Nat) (place : Place) (symval : Nat) :
  stepEvent st (.mutBorrow loan place symval .direct) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval .direct) Ω ∧
        LStep Ω (.mutBorrow loan place symval .direct) Ω' ∧
        concretise st' = Ω' := by
  sorry

/-- M9.6 hint case: `kind_hint = MbkInAbsReborrow abs` triggers
    `Le-Reborrow-MutBorrow-Abs` (paper Fig. 8) on the named abs.
    Closed by Phase-C M10.2i. -/
theorem stepMutBorrow_inAbsReborrow_sound
  (loan : Nat) (place : Place) (symval : Nat) (absId : Nat) :
  stepEvent st
    (.mutBorrow loan place symval (.inAbsReborrow absId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω' ∧
        concretise st' = Ω' := by
  sorry

/-- M9.6 hint case: `kind_hint = MbkLoopOwned loop` triggers the
    loop-fixpoint borrow rule (paper §5.2). Closed by Phase-C
    M10.2j. -/
theorem stepMutBorrow_loopOwned_sound
  (loan : Nat) (place : Place) (symval : Nat) (loopId : Nat) :
  stepEvent st
    (.mutBorrow loan place symval (.loopOwned loopId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.loopOwned loopId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.loopOwned loopId)) Ω' ∧
        concretise st' = Ω' := by
  sorry

/-- `EvJoin { witnesses }` triggers the conjunction of the Fig. 11
    rules named by each witness. Per-entry induction over
    [witnesses] is the heart of the join soundness proof. Closed by
    Phase-C M10.2r–w. -/
theorem stepJoin_witnessed_sound
  (left right result : StateSummary) (witnesses : Array JoinEntry) :
  stepEvent st (.join left right result witnesses) = .ok st' →
  ∃ Ω', Valid (.join left right result witnesses) Ω ∧
        LStep Ω (.join left right result witnesses) Ω' ∧
        concretise st' = Ω' := by
  sorry

end StepEvent

/-! ## Top-level: `stepEvent_sound`

Case-analysis on `ev`. Hint-bearing events sub-case on the hint and
delegate to the per-rule lemma above; non-hinted events apply their
single-rule lemma directly. Closed by Phase-D M10.3a (which assembles
the per-event lemmas added across Phase C). -/

theorem stepEvent_sound :
    ∀ (ev : Event) (st st' : SymState) (Ω : LLBCState),
      concretise st = Ω →
      stepEvent st ev = .ok st' →
      ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ concretise st' = Ω' := by
  sorry

/-! ## Cross-cutting consequences (sketched in
`cert-format-and-soundness.md` §4.3 / §4.4)

* `replayFun_sound` — induction on the events array, threading the
  per-event lemma through. Lands in
  `AeneasSoundness/Soundness/ReplayFunSound.lean` (Phase E).
* `replayCrate_implies_borrow_checks` — quantify `replayFun_sound`
  over `cc.functions`. Lands in
  `AeneasSoundness/Soundness/ReplayCrateSound.lean` (Phase F).
-/

end AeneasSoundness.Soundness
