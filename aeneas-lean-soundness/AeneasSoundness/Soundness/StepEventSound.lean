import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.LLBCSharpPaper.Step
import AeneasSoundness.LLBCSharpPaper.Valid
import AeneasSoundness.Soundness.Concretise.Defn
import AeneasSoundness.Soundness.Concretise.Lemmas

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

/-! ## Concretisation

M10.0k introduced `concretise` as a placeholder. M10.1a moves the
real definition into `Concretise/Defn.lean` (env + numLocals half);
M10.1b lands the rest (loans + absRegistry). This file re-exports
the name so per-event lemma signatures stay short. -/

/-- Re-export of `Concretise.concretise` so per-event lemma
    signatures (and Phase D's `stepEvent_sound`) can write
    `concretise st` directly. -/
abbrev concretise : SymState → LLBCState := Concretise.concretise

/-! ## Per-event sub-soundness lemmas -/

section StepEvent

variable (st st' : SymState) (Ω : LLBCState)
variable (hRep : concretise st = Ω)

/-- C1 / M10.2a — `E-Panic` (paper Fig. 3). `stepEvent st .panic`
    returns `st` unchanged; we witness `Ω' = Ω`, `LStep.panic`, and
    transport `hRep` along the `st = st'` equality the replayer
    exposes. `Valid .panic Ω = True`. -/
theorem stepPanic_sound (hRep : concretise st = Ω) :
  stepEvent st .panic = .ok st' →
  ∃ Ω', Valid .panic Ω ∧ LStep Ω .panic Ω' ∧ concretise st' = Ω' := by
  intro h
  simp only [stepEvent, Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨Ω, trivial, LStep.panic, hRep⟩

/-- C1 / M10.2a — `E-Step-Return` (paper Fig. 7). Symmetric to
    `stepPanic_sound`: `stepEvent st .retn` is `return st`, so the
    replayer leaves the state unchanged. `Valid .retn Ω = True`. -/
theorem stepRetn_sound (hRep : concretise st = Ω) :
  stepEvent st .retn = .ok st' →
  ∃ Ω', Valid .retn Ω ∧ LStep Ω .retn Ω' ∧ concretise st' = Ω' := by
  intro h
  simp only [stepEvent, Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨Ω, trivial, LStep.retn, hRep⟩

/-- C2 / M10.2b — match-arm marker. `stepEvent` reduces `.matchArm`
    to `return st`; on the paper side `LStep.matchArm` is a no-op. -/
theorem stepMatchArm_sound (hRep : concretise st = Ω)
  (scrutinee : SymExpr) (adtId variantId : Nat) (variantName : String) :
  stepEvent st (.matchArm scrutinee adtId variantId variantName) = .ok st' →
  ∃ Ω', Valid (.matchArm scrutinee adtId variantId variantName) Ω ∧
        LStep Ω (.matchArm scrutinee adtId variantId variantName) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨Ω, trivial, LStep.matchArm, hRep⟩

/-- C2 / M10.2b — end-of-loop-iteration marker. Symmetric to
    `stepMatchArm_sound`. The full loop semantics lives in
    `stepLoopInv_sound` (C17). -/
theorem stepLoopEnd_sound (hRep : concretise st = Ω) (loopId : Nat) :
  stepEvent st (.loopEnd loopId) = .ok st' →
  ∃ Ω', Valid (.loopEnd loopId) Ω ∧
        LStep Ω (.loopEnd loopId) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨Ω, trivial, LStep.loopEnd, hRep⟩

/-! ### Move / Copy

`stepMove` / `stepCopy` operate on the root local of `src` /
`dst` (`placeRootLocal p = p.local_`), ignoring any projection.
For the paper-side `LStep.move` / `LStep.copy` premise
(`resolvePlace src = some v`) to fire under that semantics we
require:

* `src.projection = #[]` — projection-empty, so
  `resolvePlace src = getLocal src.local_`.
* `dst.projection = #[]` — symmetric assumption on the destination.
* `(st.env[src.local_]?).isSome` — `src.local_` is declared in
  the replayer's env, so `liftEnv` maps it to `some (liftVal _)`.

The three hypotheses are *Phase-D-dischargeable* — the cert's
emission discipline (root-only places for move / copy) is enforced
either by `WellFormedProgram` / `CertGen_faithful` or by a future
checker-side pre-pass. Until then Phase D / Phase F threads them
through the case-split. -/

/-- C3 / M10.2c — `E-Move`. Replayer `stepMove` performs
    `setLocal src.local_ .bottom; setLocal dst.local_ v` where
    `v := st.env.getD src.local_ .bottom`. The paper-side
    `LStep.move` mutates the same fields; we witness `v` as
    `liftVal vR` where `vR` is the replayer-observed value. -/
theorem stepMove_sound
  (hRep : concretise st = Ω)
  (src dst : Place)
  (hSrcProj : src.projection = #[])
  (_hDstProj : dst.projection = #[])
  (hSrcEnv : ∃ v, st.env[src.local_]? = some v) :
  stepEvent st (.move src dst) = .ok st' →
  ∃ Ω', Valid (.move src dst) Ω ∧
        LStep Ω (.move src dst) Ω' ∧
        concretise st' = Ω' := by
  obtain ⟨vR, hvR⟩ := hSrcEnv
  intro h
  -- The replayer's stepMove is a pure pipeline of two setLocals.
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMove,
    AeneasCheck.LLBCSharp.placeRootLocal, AeneasCheck.LLBCSharp.SymState.getLocal,
    Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- Common fact: `Ω.resolvePlace src = some (liftVal vR)`.
  have hResolve : Ω.resolvePlace src = some (Concretise.liftVal vR) := by
    subst hRep
    simp [LLBCState.resolvePlace, hSrcProj, LLBCState.resolveProj,
      LLBCState.getLocal, Concretise.concretise, Concretise.liftEnv, hvR]
  refine ⟨(Ω.setLocal src.local_ .bottom).setLocal dst.local_ (Concretise.liftVal vR),
          ⟨_, hResolve⟩, LStep.move hResolve, ?_⟩
  -- concretise st' = Ω' via two setLocal commutes; the source value
  -- coincides with `liftVal vR` because `st.env[src.local_]? = some vR`.
  have hGetD : (st.env.getD src.local_ (.bottom : Val)) = vR := by
    rw [Std.HashMap.getD_eq_getD_getElem?, hvR]; rfl
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    Concretise.concretise_setLocal, hRep, hGetD, Concretise.liftVal]

/-- C3 / M10.2c — `E-Copy`. Like `stepMove_sound` but the source is
    not cleared; the replayer's `stepCopy` performs a single
    `setLocal dst.local_ v`. -/
theorem stepCopy_sound
  (hRep : concretise st = Ω)
  (src dst : Place)
  (hSrcProj : src.projection = #[])
  (_hDstProj : dst.projection = #[])
  (hSrcEnv : ∃ v, st.env[src.local_]? = some v) :
  stepEvent st (.copy src dst) = .ok st' →
  ∃ Ω', Valid (.copy src dst) Ω ∧
        LStep Ω (.copy src dst) Ω' ∧
        concretise st' = Ω' := by
  obtain ⟨vR, hvR⟩ := hSrcEnv
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepCopy,
    AeneasCheck.LLBCSharp.placeRootLocal, AeneasCheck.LLBCSharp.SymState.getLocal,
    Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hResolve : Ω.resolvePlace src = some (Concretise.liftVal vR) := by
    subst hRep
    simp [LLBCState.resolvePlace, hSrcProj, LLBCState.resolveProj,
      LLBCState.getLocal, Concretise.concretise, Concretise.liftEnv, hvR]
  refine ⟨Ω.setLocal dst.local_ (Concretise.liftVal vR),
          ⟨_, hResolve⟩, LStep.copy hResolve, ?_⟩
  have hGetD : (st.env.getD src.local_ (.bottom : Val)) = vR := by
    rw [Std.HashMap.getD_eq_getD_getElem?, hvR]; rfl
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    Concretise.concretise_setLocal, hRep, hGetD]

/-- C4 / M10.2d — `E-Assign`. The replayer's `stepAssign` evaluates
    `rhs` via `evalSymExpr` (which is total — every `SymExpr` constructor
    has a `return` branch) and `setLocal`s the destination. We witness
    the paper-side existential `v` as `liftVal vR` where `vR` is the
    evaluated rhs. `Valid (.assign _ _) = True`. -/
theorem stepAssign_sound
  (hRep : concretise st = Ω)
  (dst : Place) (rhs : SymExpr) :
  stepEvent st (.assign dst rhs) = .ok st' →
  ∃ Ω', Valid (.assign dst rhs) Ω ∧
        LStep Ω (.assign dst rhs) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepAssign, bind, Except.bind,
    AeneasCheck.LLBCSharp.placeRootLocal] at h
  -- Case on the evalSymExpr result; the .error branch contradicts `h`.
  match heval : AeneasCheck.LLBCSharp.evalSymExpr st rhs with
  | .error _ => rw [heval] at h; cases h
  | .ok vR =>
    rw [heval] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨Ω.setLocal dst.local_ (Concretise.liftVal vR), trivial, LStep.assign, ?_⟩
    simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
      Concretise.concretise_setLocal, hRep]

/-- C5 / M10.2e — `E-Assert`. The dispatcher routes `.assert` to
    `let _ ← stepAssert ...; return st`, so on success `st' = st`.
    The paper has two `LStep` constructors (`assert_true`,
    `assert_false_panic`) keyed by the `expected` bool; we case on
    `expected` to pick the right one. `Valid (.assert _ _) = True`. -/
theorem stepAssert_sound
  (hRep : concretise st = Ω)
  (cond : SymExpr) (expected : Bool) :
  stepEvent st (.assert cond expected) = .ok st' →
  ∃ Ω', Valid (.assert cond expected) Ω ∧
        LStep Ω (.assert cond expected) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, bind, Except.bind] at h
  match heval : AeneasCheck.LLBCSharp.stepAssert st cond expected with
  | .error _ => rw [heval] at h; cases h
  | .ok _ =>
    rw [heval] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨Ω, trivial, ?_, hRep⟩
    cases expected
    · exact LStep.assert_false_panic
    · exact LStep.assert_true

/-- C6 / M10.2f — `E-BinaryOp`. The replayer's `stepBinop` evaluates
    both operands (`evalSymExpr` is total — both `let _ ← ...` binds
    succeed), bounds-checks `dst.local_ < numLocals`, and writes
    `.sym 0` to the destination. We witness σ = 0 in `LStep.binop`;
    the freshness premise `Ω.symValIdFresh 0` is `0 ≤ 0` which holds
    because `concretise` sets `nextSymValId := 0`. `bumpSymValId`'s
    redefinition as a no-op (preceding commit material in State.lean)
    is what makes `concretise st' = Ω'` close. -/
theorem stepBinop_sound
  (hRep : concretise st = Ω)
  (op : String) (lhs rhs : SymExpr) (dst : Place) :
  stepEvent st (.binop op lhs rhs dst) = .ok st' →
  ∃ Ω', Valid (.binop op lhs rhs dst) Ω ∧
        LStep Ω (.binop op lhs rhs dst) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepBinop, bind, Except.bind,
    AeneasCheck.LLBCSharp.placeRootLocal] at h
  -- Two evalSymExpr binds and a numLocals bounds check.
  match heval1 : AeneasCheck.LLBCSharp.evalSymExpr st lhs with
  | .error _ => rw [heval1] at h; cases h
  | .ok _ =>
  rw [heval1] at h
  match heval2 : AeneasCheck.LLBCSharp.evalSymExpr st rhs with
  | .error _ => rw [heval2] at h; cases h
  | .ok _ =>
  rw [heval2] at h
  by_cases hBounds : dst.local_ ≥ st.numLocals
  · -- bounds-check failure: `fail _ = .error _`, contradicts h
    simp only [hBounds, ite_true] at h
    cases h
  · simp only [hBounds, ite_false, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- Witness σ = 0; freshness premise is `0 ≤ 0`.
    have hFresh : Ω.symValIdFresh 0 := by
      subst hRep
      simp [LLBCState.symValIdFresh, Concretise.concretise]
    refine ⟨Ω.setLocal dst.local_ (.sym 0), ⟨0, hFresh⟩,
            (LStep.binop hFresh : LStep Ω (.binop op lhs rhs dst) _), ?_⟩
    -- bumpSymValId is a no-op, so the target reduces.
    simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
      Concretise.concretise_setLocal, hRep, Concretise.liftVal]

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
