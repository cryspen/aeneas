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

/-! ### Shared borrow

`stepSharedBorrow` is the first per-event lemma to consume
`concretise_addLoan` (M10.1f; M10.1h made it unconditional).
Like the move / copy lemmas it takes three Phase-D-dischargeable
hypotheses: the place's projection is empty, the local is
declared, and the loan id is strictly fresh w.r.t. the
replayer's monotone loan-id HWM (`st.loanIdHwm ≤ loan`). The
freshness premise matches `LStep`'s `loanIdFresh` premise via
the `concretise` lift; cert emission discipline (monotone id
allocation) discharges it. -/

/-- C7 / M10.2g — `E-SharedBorrow` (paper Fig. 3). The replayer
    fails if the loan id is already live or the place's root is
    out of range, otherwise records the new shared loan; on the
    paper side this picks `LStep.sharedBorrow`, witnessing the
    inner value as `liftVal vR`. -/
theorem stepSharedBorrow_sound
  (hRep : concretise st = Ω)
  (loan sbId : Nat) (place : Place) (symval : Nat)
  (hPlaceProj : place.projection = #[])
  (hPlaceEnv : ∃ v, st.env[place.local_]? = some v)
  (hLoanFresh : st.loanIdHwm ≤ loan) :
  stepEvent st (.sharedBorrow loan sbId place symval) = .ok st' →
  ∃ Ω', Valid (.sharedBorrow loan sbId place symval) Ω ∧
        LStep Ω (.sharedBorrow loan sbId place symval) Ω' ∧
        concretise st' = Ω' := by
  obtain ⟨vR, hvR⟩ := hPlaceEnv
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepSharedBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal,
    AeneasCheck.LLBCSharp.SymState.getLocal] at h
  -- Guard 1: `st.loans.contains loan = false` (on success).
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    -- Guard 2: `place.local_ < st.numLocals` (on success).
    by_cases hB : place.local_ ≥ st.numLocals
    · rw [if_pos hB] at h; cases h
    · rw [if_neg hB] at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      -- Witness Ω' = (Ω.bumpLoanId loan).bumpSymValId symval.
      have hResolve : Ω.resolvePlace place = some (Concretise.liftVal vR) := by
        subst hRep
        simp [LLBCState.resolvePlace, hPlaceProj, LLBCState.resolveProj,
          LLBCState.getLocal, Concretise.concretise, Concretise.liftEnv, hvR]
      have hLoanIdFresh : Ω.loanIdFresh loan := by
        subst hRep
        simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
      have hSymValIdFresh : Ω.symValIdFresh symval := by
        subst hRep
        simp [LLBCState.symValIdFresh, Concretise.concretise]
      refine ⟨(Ω.bumpLoanId loan).bumpSymValId symval,
              ⟨⟨_, hResolve⟩, hLoanIdFresh, hSymValIdFresh⟩,
              LStep.sharedBorrow hResolve hLoanIdFresh hSymValIdFresh, ?_⟩
      -- concretise (st.addLoan loan vR .shared) = Ω.bumpLoanId loan
      -- (bumpSymValId is a no-op).
      have hGetD :
        (st.env.getD place.local_ (.bottom : Val)) = vR := by
        rw [Std.HashMap.getD_eq_getD_getElem?, hvR]; rfl
      simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
        hGetD, LLBCState.bumpSymValId,
        Concretise.concretise_addLoan, hRep]

/-- C8 / M10.2h — `EvMutBorrow { kind_hint = MbkDirect }` triggers
    `E-MutBorrow` (paper Fig. 3). The replayer additionally replaces
    `place.local_` by a `mutLoan loan` token; we chain
    `concretise_setLocal` and `concretise_addLoan` to discharge the
    post-state equality. Same Phase-D-dischargeable hypotheses as
    `stepSharedBorrow_sound`. -/
theorem stepMutBorrow_direct_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (place : Place) (symval : Nat)
  (hPlaceProj : place.projection = #[])
  (hPlaceEnv : ∃ v, st.env[place.local_]? = some v)
  (hLoanFresh : st.loanIdHwm ≤ loan) :
  stepEvent st (.mutBorrow loan place symval .direct) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval .direct) Ω ∧
        LStep Ω (.mutBorrow loan place symval .direct) Ω' ∧
        concretise st' = Ω' := by
  obtain ⟨vR, hvR⟩ := hPlaceEnv
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMutBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal,
    AeneasCheck.LLBCSharp.SymState.getLocal] at h
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    by_cases hB : place.local_ ≥ st.numLocals
    · rw [if_pos hB] at h; cases h
    · rw [if_neg hB] at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hResolve : Ω.resolvePlace place = some (Concretise.liftVal vR) := by
        subst hRep
        simp [LLBCState.resolvePlace, hPlaceProj, LLBCState.resolveProj,
          LLBCState.getLocal, Concretise.concretise, Concretise.liftEnv, hvR]
      have hLoanIdFresh : Ω.loanIdFresh loan := by
        subst hRep
        simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
      have hSymValIdFresh : Ω.symValIdFresh symval := by
        subst hRep
        simp [LLBCState.symValIdFresh, Concretise.concretise]
      refine ⟨((Ω.setLocal place.local_ (.mutLoan loan)).bumpLoanId loan).bumpSymValId symval,
              ⟨⟨_, hResolve⟩, hLoanIdFresh, hSymValIdFresh⟩,
              LStep.mutBorrow_direct hResolve hLoanIdFresh hSymValIdFresh, ?_⟩
      -- concretise ((st.setLocal _ (.mutLoan loan)).addLoan loan _ .direct)
      --   = (Ω.setLocal _ (.mutLoan loan)).bumpLoanId loan  (bumpSymValId no-op)
      -- setLocal preserves `.loans` (it only mutates `env`), so the
      -- freshness premise carries over without any transport.
      have hGetD :
        (st.env.getD place.local_ (.bottom : Val)) = vR := by
        rw [Std.HashMap.getD_eq_getD_getElem?, hvR]; rfl
      simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
        hGetD, LLBCState.bumpSymValId,
        Concretise.concretise_addLoan,
        Concretise.concretise_setLocal, hRep, Concretise.liftVal]

/-- C9 / M10.2i — `EvMutBorrow { kind_hint = MbkInAbsReborrow abs }`
    triggers `Le-Reborrow-MutBorrow-Abs` (paper Fig. 8) on the named
    abs. The replayer records a `.reborrow`-kind loan but leaves `env`
    untouched, so this discharge only needs `concretise_addLoan`. The
    `hAbsExists` hypothesis is the Phase-D-dischargeable replacement
    for the `Ω.abs absId = some r` premise. -/
theorem stepMutBorrow_inAbsReborrow_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (place : Place) (symval : Nat) (absId : Nat)
  (hAbsExists : ∃ r, st.absRegistry[absId]? = some r)
  (hLoanFresh : st.loanIdHwm ≤ loan) :
  stepEvent st
    (.mutBorrow loan place symval (.inAbsReborrow absId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω' ∧
        concretise st' = Ω' := by
  obtain ⟨r, hr⟩ := hAbsExists
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMutBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal] at h
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    by_cases hB : place.local_ ≥ st.numLocals
    · rw [if_pos hB] at h; cases h
    · rw [if_neg hB] at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hAbsLifted : Ω.abs absId = some (LLBCSharpPaper.liftAbsShape r) := by
        subst hRep
        simp [Concretise.concretise, Concretise.liftAbsRegistry, hr]
      have hLoanIdFresh : Ω.loanIdFresh loan := by
        subst hRep
        simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
      have hSymValIdFresh : Ω.symValIdFresh symval := by
        subst hRep
        simp [LLBCState.symValIdFresh, Concretise.concretise]
      refine ⟨(Ω.bumpLoanId loan).bumpSymValId symval,
              ⟨⟨_, hAbsLifted⟩, hLoanIdFresh, hSymValIdFresh⟩,
              LStep.mutBorrow_inAbsReborrow hAbsLifted hLoanIdFresh hSymValIdFresh, ?_⟩
      simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
        LLBCState.bumpSymValId,
        Concretise.concretise_addLoan, hRep]

/-- C10 / M10.2j — `EvMutBorrow { kind_hint = MbkLoopOwned loop }`
    triggers the loop-fixpoint borrow rule (paper §5.2). Same shape
    as `stepMutBorrow_direct_sound`: the replayer additionally writes
    a `mutLoan` token to `place.local_`. The replayer's recorded kind
    is `.lazyExpand` (distinct from `.direct`) but `concretise_addLoan`
    is kind-agnostic. -/
theorem stepMutBorrow_loopOwned_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (place : Place) (symval : Nat) (loopId : Nat)
  (hPlaceProj : place.projection = #[])
  (hPlaceEnv : ∃ v, st.env[place.local_]? = some v)
  (hLoanFresh : st.loanIdHwm ≤ loan) :
  stepEvent st
    (.mutBorrow loan place symval (.loopOwned loopId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.loopOwned loopId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.loopOwned loopId)) Ω' ∧
        concretise st' = Ω' := by
  obtain ⟨vR, hvR⟩ := hPlaceEnv
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMutBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal,
    AeneasCheck.LLBCSharp.SymState.getLocal] at h
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    by_cases hB : place.local_ ≥ st.numLocals
    · rw [if_pos hB] at h; cases h
    · rw [if_neg hB] at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hResolve : Ω.resolvePlace place = some (Concretise.liftVal vR) := by
        subst hRep
        simp [LLBCState.resolvePlace, hPlaceProj, LLBCState.resolveProj,
          LLBCState.getLocal, Concretise.concretise, Concretise.liftEnv, hvR]
      have hLoanIdFresh : Ω.loanIdFresh loan := by
        subst hRep
        simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
      have hSymValIdFresh : Ω.symValIdFresh symval := by
        subst hRep
        simp [LLBCState.symValIdFresh, Concretise.concretise]
      refine ⟨((Ω.setLocal place.local_ (.mutLoan loan)).bumpLoanId loan).bumpSymValId symval,
              ⟨⟨_, hResolve⟩, hLoanIdFresh, hSymValIdFresh⟩,
              LStep.mutBorrow_loopOwned hResolve hLoanIdFresh hSymValIdFresh, ?_⟩
      have hGetD :
        (st.env.getD place.local_ (.bottom : Val)) = vR := by
        rw [Std.HashMap.getD_eq_getD_getElem?, hvR]; rfl
      simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
        hGetD, LLBCState.bumpSymValId,
        Concretise.concretise_addLoan,
        Concretise.concretise_setLocal, hRep, Concretise.liftVal]

/-! ### End-borrow trio (C11-C13)

`stepEndBorrow` reads the cert's `restore.givenBack` and dispatches
on the live loan's `LoanKind`. The three soundness lemmas mirror
the three `LStep.endBorrow_*` constructors:

* `.direct` / `.lazyExpand` → `LStep.endBorrow_direct`: the unique
  local holding `mutLoan loan` is set to the given-back value;
  the paper side picks `(Ω.setLocal x v)`.
* `.reborrow` → `LStep.endBorrow_reborrow`: env untouched, Ω unchanged.
* `.shared` → `LStep.endBorrow_shared`: env untouched, Ω unchanged.

Each lemma takes a Phase-D-dischargeable *result-shape* hypothesis
that pins the replayer's post-state. This avoids unrolling the
env-scan `for ... in st.env.toList` loop here; Phase D (or a
follow-up M9.8 micro-bump if needed) discharges it from the
`LoanTokenInvariant` uniqueness fact + cert emission discipline. -/

/-- C11 / M10.2k — `EvEndBorrow` with `.direct` (or `.lazyExpand`)
    loan kind triggers `Reorg-End-MutBorrow` (paper Fig. 3). The
    Phase-D-dischargeable `hShape` hypothesis pins the result of
    `stepEndBorrow` to a single setLocal of the unique
    `mutLoan loan`-holding local with the cert's given-back value;
    `hHolder` lifts the holder local to the paper-side `Ω.ctx`
    side. Both are Phase-D-dischargeable via the `LoanTokenInvariant`
    that pairs the replayer's `mutLoan` token positions with the
    paper's `ctx`. -/
theorem stepEndBorrow_direct_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (restore : RestoreInfo)
  (x : Nat) (v : AeneasCheck.LLBCSharp.Val) (stTake : SymState)
  (hTake : ∃ li : LoanInfo,
    st.takeLoan loan = some (li, stTake) ∧
    (li.kind = .direct ∨ li.kind = .lazyExpand))
  (hHolder : Ω.ctx x = some (.mutLoan loan))
  (hShape : stepEvent st (.endBorrow loan restore) =
            .ok (stTake.setLocal x v)) :
  stepEvent st (.endBorrow loan restore) = .ok st' →
  ∃ Ω', Valid (.endBorrow loan restore) Ω ∧
        LStep Ω (.endBorrow loan restore) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Result-shape collapses st' = stTake.setLocal x v.
  rw [hShape] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  obtain ⟨li, hTakeOk, _hKind⟩ := hTake
  -- concretise stTake = concretise st (takeLoan commute; M10.1h).
  have hConc : concretise stTake = concretise st :=
    Concretise.concretise_takeLoan _ _ hTakeOk
  -- Witness Ω' := Ω.setLocal x (liftVal v). LStep.endBorrow_direct
  -- consumes `hHolder` and pins its existential `v` field to
  -- `liftVal v`.
  refine ⟨Ω.setLocal x (Concretise.liftVal v),
          trivial,
          (LStep.endBorrow_direct hHolder :
            LStep Ω (.endBorrow loan restore)
              (Ω.setLocal x (Concretise.liftVal v))),
          ?_⟩
  -- concretise (stTake.setLocal x v) = Ω.setLocal x (liftVal v)
  -- via concretise_setLocal + concretise_takeLoan + hRep.
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    Concretise.concretise_setLocal, hConc, hRep]

/-- C12 / M10.2l — `EvEndBorrow` with `.reborrow` loan kind. The
    replayer's `stepEndBorrow` releases the loan id (via `takeLoan`)
    but leaves env unchanged; the paper side picks
    `LStep.endBorrow_reborrow`, whose post-state equals the
    pre-state. -/
theorem stepEndBorrow_reborrow_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (restore : RestoreInfo) (stTake : SymState)
  (hTake : ∃ li : LoanInfo,
    st.takeLoan loan = some (li, stTake) ∧ li.kind = .reborrow)
  (hShape : stepEvent st (.endBorrow loan restore) = .ok stTake) :
  stepEvent st (.endBorrow loan restore) = .ok st' →
  ∃ Ω', Valid (.endBorrow loan restore) Ω ∧
        LStep Ω (.endBorrow loan restore) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  rw [hShape] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  obtain ⟨_li, hTakeOk, _hKind⟩ := hTake
  refine ⟨Ω, trivial, LStep.endBorrow_reborrow, ?_⟩
  exact (Concretise.concretise_takeLoan _ _ hTakeOk).trans hRep

/-- C13 / M10.2m — `EvEndBorrow` with `.shared` loan kind. Same
    shape as C12: env untouched, Ω unchanged. The paper side picks
    `LStep.endBorrow_shared`. -/
theorem stepEndBorrow_shared_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (restore : RestoreInfo) (stTake : SymState)
  (hTake : ∃ li : LoanInfo,
    st.takeLoan loan = some (li, stTake) ∧ li.kind = .shared)
  (hShape : stepEvent st (.endBorrow loan restore) = .ok stTake) :
  stepEvent st (.endBorrow loan restore) = .ok st' →
  ∃ Ω', Valid (.endBorrow loan restore) Ω ∧
        LStep Ω (.endBorrow loan restore) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  rw [hShape] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  obtain ⟨_li, hTakeOk, _hKind⟩ := hTake
  refine ⟨Ω, trivial, LStep.endBorrow_shared, ?_⟩
  exact (Concretise.concretise_takeLoan _ _ hTakeOk).trans hRep

/-! ### Reborrow (C14)

`stepReborrow` allocates a fresh child loan id. The replayer's M9.6
strict path pre-adds the parent as a `.reborrow` loan if it isn't
already in `st.loans` (covers the case where the cert's parent loan
lives inside an abs the replayer doesn't model). The paper's
`LStep.reborrow` post-state is just `Ω.bumpLoanId child`; the
parent-pre-add is invisible on the paper side as long as `parent <
Ω.freshness.nextLoanId` (i.e. parent was previously allocated and
the HWM is already past it) — making `Ω.bumpLoanId parent = Ω` a
no-op. Both branches collapse to the same paper-side conclusion. -/

/-- C14 / M10.2n — `EvReborrow child parent place …` triggers
    `Le-Reborrow-MutBorrow-Abs` (paper Fig. 8 body-position entry).
    Two Phase-D-dischargeable freshness premises:
    * `hChildFresh : st.loanIdHwm ≤ child` — matches the paper's
      `loanIdFresh child` premise after the `concretise` lift.
    * `hParentInHwm : parent < st.loanIdHwm` — used to discharge
      the no-op `Ω.bumpLoanId parent = Ω` when the replayer's
      strict-path falls through to the pre-add-parent branch. Cert
      emission discipline (parent loan id was previously allocated)
      discharges. -/
theorem stepReborrow_sound
  (hRep : concretise st = Ω)
  (child parent : Nat) (place : Place)
  (parentLive : Bool) (parentAbs : Option Nat)
  (hChildFresh : st.loanIdHwm ≤ child)
  (hParentInHwm : parent < st.loanIdHwm) :
  stepEvent st (.reborrow child parent place parentLive parentAbs)
    = .ok st' →
  ∃ Ω', Valid (.reborrow child parent place parentLive parentAbs) Ω ∧
        LStep Ω (.reborrow child parent place parentLive parentAbs) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepReborrow,
    AeneasCheck.LLBCSharp.placeRootLocal] at hStep
  -- Guard 1: child id is not already live.
  by_cases hC : st.loans.contains child = true
  · rw [if_pos hC] at hStep; cases hStep
  · rw [if_neg hC] at hStep
    -- Guard 2: place's root local is in bounds.
    by_cases hB : place.local_ ≥ st.numLocals
    · rw [if_pos hB] at hStep; cases hStep
    · rw [if_neg hB] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      -- Paper-side freshness on the child id.
      have hChildIdFresh : Ω.loanIdFresh child := by
        subst hRep
        simpa [LLBCState.loanIdFresh, Concretise.concretise] using hChildFresh
      -- Paper-side bumpLoanId is a no-op on `parent` since parent
      -- is already past the HWM.
      have hParentNoOp : Ω.bumpLoanId parent = Ω := by
        unfold LLBCState.bumpLoanId
        have hParentHwm : parent < Ω.freshness.nextLoanId := by
          subst hRep
          simpa [Concretise.concretise] using hParentInHwm
        rcases Ω with ⟨ctx, abs, ⟨nL, nA, nS⟩⟩
        simp only at *
        have : max nL (parent + 1) = nL :=
          Nat.max_eq_left (Nat.succ_le_of_lt hParentHwm)
        simp [this]
      refine ⟨Ω.bumpLoanId child,
              hChildIdFresh,
              LStep.reborrow hChildIdFresh, ?_⟩
      -- Both replayer branches conclude `?.addLoan child .bottom .reborrow`.
      -- Push concretise through the outer addLoan unconditionally.
      by_cases hP : st.loans.contains parent = true
      · rw [if_pos hP]
        simp only [show (concretise : SymState → LLBCState)
                            = Concretise.concretise from rfl,
          Concretise.concretise_addLoan, hRep]
      · rw [if_neg hP]
        simp only [show (concretise : SymState → LLBCState)
                            = Concretise.concretise from rfl,
          Concretise.concretise_addLoan, hParentNoOp, hRep]

/-! ### Call (C15, full absSig support)

`stepCall` folds the cert's `absSig` into `absRegistry` (via
`SymState.addAbsShape`) and then writes a fresh `Val.sym 0` to the
dst local. Post-M10.0m the paper-side `LStep.call`'s post-state
mirrors exactly that shape: `absSig.foldl installAbsShapePaper`
followed by `setLocal dst.local_ (.sym σ)` and `bumpSymValId σ`.
The soundness proof chains `Concretise.concretise_foldl_addAbsShape`
to push `concretise` through the fold, then `concretise_setLocal`
and `liftVal (.sym 0) = .sym 0` for the final dst-write. The
empty-absSig caveat from M10.2o is gone — both the empty and
non-empty cases discharge by the same proof. -/

/-- C15 / M10.2o-revised — `EvCall fn callId fnName args dst regionAbs
    absSig` for arbitrary `absSig`. The replayer's `stepCall` and the
    paper's `LStep.call` post-states agree pointwise after M10.0m. -/
theorem stepCall_sound
  (hRep : concretise st = Ω)
  (fn callId : Nat) (fnName : String) (args : Array SymExpr)
  (dst : Place) (regionAbs : Array Nat) (absSig : Array AbsShape)
  (hDstInBounds : dst.local_ < st.numLocals) :
  stepEvent st
    (.call fn callId fnName args dst regionAbs absSig) = .ok st' →
  ∃ Ω', Valid (.call fn callId fnName args dst regionAbs absSig) Ω ∧
        LStep Ω (.call fn callId fnName args dst regionAbs absSig) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Replayer = absSig.foldl addAbsShape ; setLocal root (.sym 0).
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepCall,
    AeneasCheck.LLBCSharp.placeRootLocal] at hStep
  -- Guard: dst's root is in bounds.
  have hNotGE : ¬ dst.local_ ≥ st.numLocals := Nat.not_le_of_lt hDstInBounds
  rw [if_neg hNotGE] at hStep
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
  subst hStep
  -- Paper-side σ := 0 freshness (concretise sets nextSymValId := 0).
  have hSymValIdFresh : Ω.symValIdFresh 0 := by
    subst hRep
    simp [LLBCState.symValIdFresh, Concretise.concretise]
  -- Witness: paper-side post-state = fold-then-setLocal-then-bumpSym.
  refine ⟨((absSig.foldl Concretise.installAbsShapePaper Ω).setLocal dst.local_
            (.sym 0)).bumpSymValId 0,
          ⟨0, hSymValIdFresh⟩,
          LStep.call hSymValIdFresh, ?_⟩
  -- Push concretise through setLocal, then through the addAbsShape fold,
  -- then hRep substitutes Ω; bumpSymValId is a no-op.
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    LLBCState.bumpSymValId, Concretise.concretise_setLocal,
    Concretise.concretise_foldl_addAbsShape, hRep, Concretise.liftVal]

/-! ### EndAbs (C16)

`stepEndAbs` validates the released loans against the registered
abstraction's role list, drops each released loan from `st.loans`,
clears the named `tokenClearLocals` (those holding `mutLoan _` tokens
become `.bottom`), then erases the abstraction's registry entry. On
the paper side `LStep.endAbs`'s post-state is `Ω.removeAbs abs`,
mirrored by the `concretise_removeAbsShape` commute. The intermediate
state pre-removal is folded into a single `stPre` argument plus a
Phase-D-dischargeable `hConcPre : concretise stPre = concretise st`
hypothesis (the loan-erase + token-clear together preserve
concretise; the token-clear's `.mutLoan → .bottom` substitution is
the part that needs `LoanTokenInvariant`-style discipline to be
sound at the deep-Val level — Phase D territory).

The `hShape` hypothesis pins `stepEvent` to `.ok (stPre.removeAbsShape
absId)`, matching the C11-C13 result-shape pattern. -/

/-- C16 / M10.2p — `EvEndAbs absId finalValues released tokenClearLocals`
    triggers `Reorg-End-Abs` (paper Fig. 8). Two Phase-D-dischargeable
    hypotheses: `hAbsInRegistry` lifts the abs entry to the paper
    side via `concretise.abs = liftAbsRegistry`, and the
    `(stPre, hConcPre, hShape)` triple folds the loan-erase plus
    token-clear preamble into one `concretise`-preserving step.

    Post-state matches `Ω.removeAbs absId` via
    `concretise_removeAbsShape` (M10.1i) ; `hConcPre` ; `hRep`. -/
theorem stepEndAbs_sound
  (hRep : concretise st = Ω)
  (absId : Nat) (finalValues : Array SymExpr) (releasedLoans : Array Nat)
  (tokenClearLocals : Array Nat)
  (shape : AbsShape)
  (hAbsInRegistry : st.absRegistry[absId]? = some shape)
  (stPre : SymState)
  (hConcPre : concretise stPre = concretise st)
  (hShape : stepEvent st
            (.endAbs absId finalValues releasedLoans tokenClearLocals) =
            .ok (stPre.removeAbsShape absId)) :
  stepEvent st (.endAbs absId finalValues releasedLoans tokenClearLocals) = .ok st' →
  ∃ Ω', Valid (.endAbs absId finalValues releasedLoans tokenClearLocals) Ω ∧
        LStep Ω (.endAbs absId finalValues releasedLoans tokenClearLocals) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Result-shape collapses st' = stPre.removeAbsShape absId.
  rw [hShape] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  -- Lift the registry lookup to the paper-side via hRep ; concretise.abs.
  have hAbsLifted : Ω.abs absId = some (LLBCSharpPaper.liftAbsShape shape) := by
    subst hRep
    simp [Concretise.concretise, Concretise.liftAbsRegistry, hAbsInRegistry]
  refine ⟨Ω.removeAbs absId,
          ⟨_, hAbsLifted⟩,
          LStep.endAbs hAbsLifted,
          ?_⟩
  -- concretise (stPre.removeAbsShape absId)
  --   = (concretise stPre).removeAbs absId  -- M10.1i commute
  --   = (concretise st).removeAbs absId     -- hConcPre
  --   = Ω.removeAbs absId                    -- hRep
  exact (Concretise.concretise_removeAbsShape stPre absId).trans
    (congrArg (·.removeAbs absId) (hConcPre.trans hRep))

/-! ### SymExpandMutBorrow (C17, no-substitution subset)

`stepSymExpandMutBorrow svId bid innerSv parentAbs substLocals
substLoans` walks `substLocals` rewriting any `.sym svId` env entry
to `.mutLoan bid`, walks `substLoans` doing the same to loan-given
values, then calls `addLoan bid (.sym innerSv) .lazyExpand`. The
paper's `LStep.symExpandMutBorrow` post-state is `(Ω.bumpLoanId bid).
bumpSymValId innerSv` — just freshness bumps. The substitution
itself is the deferred `SubstScope_Complete` (plan §3.4); for the
no-substitution subset (`substLocals = #[] ∧ substLoans = #[]`) the
replayer reduces to a single `addLoan` and the proof matches via
`concretise_addLoan`.

The `hBidNotInLoans` and `hBidFresh` hypotheses are
Phase-D-dischargeable from the cert's monotone loan-id discipline
(plan §11.1 #11 + the M10.1g invariant `∀ b ∈ st.loans, b <
st.loanIdHwm`). -/

/-- C17 / M10.2q — `EvSymExpandMutBorrow` (paper §4.1 lazy
    expansion). Restricted to empty `substLocals` / `substLoans`;
    the substitution-bearing case awaits a Phase-A surface
    strengthening on `LStep.symExpandMutBorrow` (deferred to the
    `SubstScope_Complete` premise per the constructor's docstring). -/
theorem stepSymExpandMutBorrow_sound
  (hRep : concretise st = Ω)
  (svId bid innerSv : Nat) (parentAbs : Option Nat)
  (substLocals substLoans : Array Nat)
  (hSubstLocalsEmpty : substLocals = #[])
  (hSubstLoansEmpty : substLoans = #[])
  (hBidNotInLoans : st.loans.contains bid = false)
  (hBidFresh : st.loanIdHwm ≤ bid) :
  stepEvent st
    (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) = .ok st' →
  ∃ Ω', Valid (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) Ω ∧
        LStep Ω (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Replayer: guard ; empty fors collapse to a single addLoan call.
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepSymExpandMutBorrow,
    hSubstLocalsEmpty, hSubstLoansEmpty] at hStep
  rw [if_neg (by simp [hBidNotInLoans])] at hStep
  simp at hStep
  -- After `simp`, hStep is `pure (X.addLoan ...) = .ok st'`, where X
  -- is the η-expanded record `{ env := st.env, ... }` (definitionally
  -- equal to `st`). Push pure→ok and η-reduce simultaneously by
  -- asserting the record equality via `rfl`.
  have hEtaSt : ({ env := st.env, loans := st.loans, numLocals := st.numLocals,
                   absRegistry := st.absRegistry, loanIdHwm := st.loanIdHwm,
                   absIdHwm := st.absIdHwm } : SymState) = st := rfl
  rw [hEtaSt] at hStep
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
  subst hStep
  -- Paper-side freshness witnesses.
  have hLoanIdFresh : Ω.loanIdFresh bid := by
    subst hRep
    simpa [LLBCState.loanIdFresh, Concretise.concretise] using hBidFresh
  have hSymValIdFresh : Ω.symValIdFresh innerSv := by
    subst hRep
    simp [LLBCState.symValIdFresh, Concretise.concretise]
  refine ⟨(Ω.bumpLoanId bid).bumpSymValId innerSv,
          ⟨hLoanIdFresh, hSymValIdFresh⟩,
          LStep.symExpandMutBorrow hLoanIdFresh hSymValIdFresh,
          ?_⟩
  -- concretise (st.addLoan bid (.sym innerSv) .lazyExpand)
  --   = (concretise st).bumpLoanId bid     -- M10.1h commute
  --   = Ω.bumpLoanId bid                    -- hRep
  --   = (Ω.bumpLoanId bid).bumpSymValId innerSv  -- bumpSymValId no-op
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    LLBCState.bumpSymValId, Concretise.concretise_addLoan, hRep]

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
