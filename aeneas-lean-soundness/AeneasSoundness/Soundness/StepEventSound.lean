import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.LLBCSharpPaper.Step
import AeneasSoundness.LLBCSharpPaper.Valid
import AeneasSoundness.Soundness.Concretise.Defn
import AeneasSoundness.Soundness.Concretise.Lemmas
import AeneasSoundness.Soundness.JoinLemmas
import AeneasSoundness.Soundness.CertGen

/-!
# Soundness of `stepEvent`

The campaign-closure file: every per-event soundness lemma (Phase C)
and the top-level `stepEvent_sound` (Phase D) live here. After
M10.3a, `stepEvent_sound` is a `theorem` — no `sorry` — proved by
case-analysis on `Event`, delegating each constructor (and sub-case
for hint-bearing events) to its per-event lemma, and discharging
each lemma's Phase-D-dischargeable hypotheses via the
`AeneasSoundness.Soundness.CertGen_faithful` family declared in
`CertGen.lean`.

## Trusted base after Phase D

`#print axioms stepEvent_sound` reports:

* `propext`, `Quot.sound`, `Classical.choice` (Lean core).
* `CertGen_faithful.join` — the last remaining OCaml-side honesty
  axiom after M10.x.9. Plan §0.3 + `CertGen.lean`'s header note are
  the audit surface. (Earlier-dropped extractors:
  `move` / `copy` in M10.x.3; `sharedBorrow` / `mutBorrow_direct` /
  `mutBorrow_loopOwned` / `reborrow` in M10.x.4;
  `mutBorrow_inAbsReborrow` in M10.x.5; `endAbs` in M10.x.6;
  `loopInv` in M10.x.7; `symExpandMutBorrow` in M10.x.8;
  `endBorrow_direct_witness` in M10.x.9;
  `call` / `endBorrow_takeOk` / `endBorrow_reborrow_witness` /
  `endBorrow_shared_witness` in M10.4a-post.)

No `sorryAx`. No domain `axiom` from `LLBCSharpPaper/`. The four
`paper_thm_*` axioms (Phase G placeholders) are not consumed by
`stepEvent_sound` and stay deferred to Phase E/F/G.

## Structure of the file

* `concretise` re-export.
* Per-event soundness lemmas (C1-C24), one section per `Event`
  constructor or hint subdivision. Each lemma takes `hRep :
  concretise st = Ω` and a small set of Phase-D-dischargeable
  hypotheses (place projection emptiness, freshness on loan / abs
  ids, result-shape hypotheses for events whose replayer body
  pre-amble doesn't fit a single commute lemma).
* `stepEvent_sound` — the top-level dispatcher.

The statement of `stepEvent_sound` mirrors plan §6.3:
```
theorem stepEvent_sound :
  ∀ ev st st' Ω, ⟦st⟧ = Ω → stepEvent st ev = .ok st' →
    ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ ⟦st'⟧ = Ω'
```
The hint-bearing events (`.mutBorrow`, `.endBorrow`) sub-case on
the hint / LoanKind; non-hinted events delegate directly. `.proj`
is dispatched by contradiction — the replayer rejects it with
`.error`, the paper's `Valid .proj` is `False`; cert v4 doesn't
emit it.
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

Both `stepMove` / `stepCopy` operate on the root local of `src` /
`dst` (`placeRootLocal p = p.local_`), ignoring any projection,
and default undeclared locals to `.bottom` via `Std.HashMap.getD`.

M10.x.3 — the paper-side `LStep.move` / `LStep.copy` rules were
re-shaped to mirror the replayer exactly: they are premise-free
and use `LLBCState.resolvePlaceRoot` (a root-local read with
`.bottom` default). This dropped the `CertGen_faithful.move` /
`.copy` extractors that were previously needed to discharge the
projection-empty + env-resident-src premises, neither of which is
guaranteed by cert emission for arbitrary fixtures (1187/1181 of
the M10.x.2 corpus violated them). -/

/-- C3 / M10.2c — `E-Move`. Replayer `stepMove` performs
    `setLocal src.local_ .bottom; setLocal dst.local_ v` where
    `v := st.env.getD src.local_ .bottom`. The paper-side
    `LStep.move` mutates the same fields; the read value
    `Ω.resolvePlaceRoot src` matches `liftVal v` by per-key
    case-split on `st.env[src.local_]?`. -/
theorem stepMove_sound
  (hRep : concretise st = Ω)
  (src dst : Place) :
  stepEvent st (.move src dst) = .ok st' →
  ∃ Ω', Valid (.move src dst) Ω ∧
        LStep Ω (.move src dst) Ω' ∧
        concretise st' = Ω' := by
  intro h
  -- The replayer's stepMove is a pure pipeline of two setLocals.
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMove,
    AeneasCheck.LLBCSharp.placeRootLocal, AeneasCheck.LLBCSharp.SymState.getLocal,
    Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨(Ω.setLocal src.local_ .bottom).setLocal dst.local_ (Ω.resolvePlaceRoot src),
          trivial, LStep.move, ?_⟩
  -- The replayer's value at the root local matches `Ω.resolvePlaceRoot src`
  -- once lifted: `Ω = concretise st` makes `Ω.ctx src.local_` reduce to
  -- `(st.env[src.local_]?).map liftVal`, so the `getD` and the `(·).getD`
  -- coincide by per-key case-split.
  have hVal : Concretise.liftVal (st.env.getD src.local_ (.bottom : Val))
              = Ω.resolvePlaceRoot src := by
    subst hRep
    simp only [LLBCState.resolvePlaceRoot, LLBCState.getLocal,
               Concretise.concretise_ctx_apply, Std.HashMap.getD_eq_getD_getElem?]
    cases hk : st.env[src.local_]? with
    | none => simp [Concretise.liftVal]
    | some v => simp
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    Concretise.concretise_setLocal, hRep, hVal, Concretise.liftVal]

/-- C3 / M10.2c — `E-Copy`. Like `stepMove_sound` but the source is
    not cleared; the replayer's `stepCopy` performs a single
    `setLocal dst.local_ v`. -/
theorem stepCopy_sound
  (hRep : concretise st = Ω)
  (src dst : Place) :
  stepEvent st (.copy src dst) = .ok st' →
  ∃ Ω', Valid (.copy src dst) Ω ∧
        LStep Ω (.copy src dst) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepCopy,
    AeneasCheck.LLBCSharp.placeRootLocal, AeneasCheck.LLBCSharp.SymState.getLocal,
    Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨Ω.setLocal dst.local_ (Ω.resolvePlaceRoot src),
          trivial, LStep.copy, ?_⟩
  have hVal : Concretise.liftVal (st.env.getD src.local_ (.bottom : Val))
              = Ω.resolvePlaceRoot src := by
    subst hRep
    simp only [LLBCState.resolvePlaceRoot, LLBCState.getLocal,
               Concretise.concretise_ctx_apply, Std.HashMap.getD_eq_getD_getElem?]
    cases hk : st.env[src.local_]? with
    | none => simp [Concretise.liftVal]
    | some v => simp
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
    Concretise.concretise_setLocal, hRep, hVal]

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
    paper side this picks `LStep.sharedBorrow`.

    M10.x.4 — every Phase-D-dischargeable hypothesis is now derived
    from `hStep` via M10.x.2's replayer reject paths
    (HWM-strengthening + projection-empty) and the paper-side
    rule's drop of the `Ω.resolvePlace p = some v` premise. The
    lemma signature carries `hRep` + `hStep` only. -/
theorem stepSharedBorrow_sound
  (hRep : concretise st = Ω)
  (loan sbId : Nat) (place : Place) (symval : Nat) :
  stepEvent st (.sharedBorrow loan sbId place symval) = .ok st' →
  ∃ Ω', Valid (.sharedBorrow loan sbId place symval) Ω ∧
        LStep Ω (.sharedBorrow loan sbId place symval) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepSharedBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal,
    AeneasCheck.LLBCSharp.SymState.getLocal] at h
  -- Guard 1: `st.loans.contains loan = false` (on success).
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    -- Guard 2 (M10.x.2): on success, `¬ st.loanIdHwm > loan`.
    by_cases hHwm : st.loanIdHwm > loan
    · rw [if_pos hHwm] at h; cases h
    · rw [if_neg hHwm] at h
      -- Guard 3 (M10.x.2): on success, `place.projection.size = 0`.
      by_cases hProj : place.projection.size ≠ 0
      · rw [if_pos hProj] at h; cases h
      · rw [if_neg hProj] at h
        -- Guard 4: `place.local_ < st.numLocals` (on success).
        by_cases hB : place.local_ ≥ st.numLocals
        · rw [if_pos hB] at h; cases h
        · rw [if_neg hB] at h
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hLoanFresh : st.loanIdHwm ≤ loan := Nat.not_lt.mp hHwm
          have hLoanIdFresh : Ω.loanIdFresh loan := by
            subst hRep
            simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
          have hSymValIdFresh : Ω.symValIdFresh symval := by
            subst hRep
            simp [LLBCState.symValIdFresh, Concretise.concretise]
          refine ⟨(Ω.bumpLoanId loan).bumpSymValId symval,
                  ⟨hLoanIdFresh, hSymValIdFresh⟩,
                  LStep.sharedBorrow hLoanIdFresh hSymValIdFresh, ?_⟩
          -- concretise (st.addLoan loan _ .shared) = Ω.bumpLoanId loan
          -- (bumpSymValId is a no-op).
          simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
            LLBCState.bumpSymValId,
            Concretise.concretise_addLoan, hRep]

/-- C8 / M10.2h — `EvMutBorrow { kind_hint = MbkDirect }` triggers
    `E-MutBorrow` (paper Fig. 3). The replayer additionally replaces
    `place.local_` by a `mutLoan loan` token; we chain
    `concretise_setLocal` and `concretise_addLoan` to discharge the
    post-state equality.

    M10.x.4 — drops `hPlaceProj` / `hPlaceEnv` (the paper-side rule
    no longer existentially binds a source value) and `hLoanFresh`
    (derived from `hStep` via M10.x.2's HWM reject path). -/
theorem stepMutBorrow_direct_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (place : Place) (symval : Nat) :
  stepEvent st (.mutBorrow loan place symval .direct) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval .direct) Ω ∧
        LStep Ω (.mutBorrow loan place symval .direct) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMutBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal,
    AeneasCheck.LLBCSharp.SymState.getLocal] at h
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    -- M10.x.2: on success, `¬ st.loanIdHwm > loan`.
    by_cases hHwm : st.loanIdHwm > loan
    · rw [if_pos hHwm] at h; cases h
    · rw [if_neg hHwm] at h
      by_cases hB : place.local_ ≥ st.numLocals
      · rw [if_pos hB] at h; cases h
      · rw [if_neg hB] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hLoanFresh : st.loanIdHwm ≤ loan := Nat.not_lt.mp hHwm
        have hLoanIdFresh : Ω.loanIdFresh loan := by
          subst hRep
          simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
        have hSymValIdFresh : Ω.symValIdFresh symval := by
          subst hRep
          simp [LLBCState.symValIdFresh, Concretise.concretise]
        refine ⟨((Ω.setLocal place.local_ (.mutLoan loan)).bumpLoanId loan).bumpSymValId symval,
                ⟨hLoanIdFresh, hSymValIdFresh⟩,
                LStep.mutBorrow_direct hLoanIdFresh hSymValIdFresh, ?_⟩
        -- concretise ((st.setLocal _ (.mutLoan loan)).addLoan loan _ .direct)
        --   = (Ω.setLocal _ (.mutLoan loan)).bumpLoanId loan  (bumpSymValId no-op).
        simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
          LLBCState.bumpSymValId,
          Concretise.concretise_addLoan,
          Concretise.concretise_setLocal, hRep, Concretise.liftVal]

/-- C9 / M10.2i — `EvMutBorrow { kind_hint = MbkInAbsReborrow abs }`
    triggers `Le-Reborrow-MutBorrow-Abs` (paper Fig. 8) on the named
    abs. The replayer records a `.reborrow`-kind loan but leaves `env`
    untouched, so this discharge only needs `concretise_addLoan`.
    M10.x.5 dropped both Phase-D hypotheses: the `∃ r, st.absRegistry[absId]?
    = some r` premise was vestigial in the paper rule (the bound `r`
    never appeared in the post-state); the `st.loanIdHwm ≤ loan` clause
    is discharged from `hStep` via M10.x.2's monotone-allocator reject
    path. -/
theorem stepMutBorrow_inAbsReborrow_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (place : Place) (symval : Nat) (absId : Nat) :
  stepEvent st
    (.mutBorrow loan place symval (.inAbsReborrow absId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.inAbsReborrow absId)) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMutBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal] at h
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    by_cases hHwm : st.loanIdHwm > loan
    · rw [if_pos hHwm] at h; cases h
    · rw [if_neg hHwm] at h
      by_cases hB : place.local_ ≥ st.numLocals
      · rw [if_pos hB] at h; cases h
      · rw [if_neg hB] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hLoanFresh : st.loanIdHwm ≤ loan := Nat.not_lt.mp hHwm
        have hLoanIdFresh : Ω.loanIdFresh loan := by
          subst hRep
          simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
        have hSymValIdFresh : Ω.symValIdFresh symval := by
          subst hRep
          simp [LLBCState.symValIdFresh, Concretise.concretise]
        refine ⟨(Ω.bumpLoanId loan).bumpSymValId symval,
                ⟨hLoanIdFresh, hSymValIdFresh⟩,
                LStep.mutBorrow_inAbsReborrow hLoanIdFresh hSymValIdFresh, ?_⟩
        simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
          LLBCState.bumpSymValId,
          Concretise.concretise_addLoan, hRep]

/-- C10 / M10.2j — `EvMutBorrow { kind_hint = MbkLoopOwned loop }`
    triggers the loop-fixpoint borrow rule (paper §5.2). Same shape
    as `stepMutBorrow_direct_sound`: the replayer additionally writes
    a `mutLoan` token to `place.local_`. The replayer's recorded kind
    is `.lazyExpand` (distinct from `.direct`) but `concretise_addLoan`
    is kind-agnostic. M10.x.4 drops all three Phase-D hypotheses
    (same shape as `stepMutBorrow_direct_sound`). -/
theorem stepMutBorrow_loopOwned_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (place : Place) (symval : Nat) (loopId : Nat) :
  stepEvent st
    (.mutBorrow loan place symval (.loopOwned loopId)) = .ok st' →
  ∃ Ω', Valid (.mutBorrow loan place symval (.loopOwned loopId)) Ω ∧
        LStep Ω (.mutBorrow loan place symval (.loopOwned loopId)) Ω' ∧
        concretise st' = Ω' := by
  intro h
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepMutBorrow,
    AeneasCheck.LLBCSharp.placeRootLocal,
    AeneasCheck.LLBCSharp.SymState.getLocal] at h
  by_cases hC : st.loans.contains loan = true
  · rw [if_pos hC] at h; cases h
  · rw [if_neg hC] at h
    -- M10.x.2: on success, `¬ st.loanIdHwm > loan`.
    by_cases hHwm : st.loanIdHwm > loan
    · rw [if_pos hHwm] at h; cases h
    · rw [if_neg hHwm] at h
      by_cases hB : place.local_ ≥ st.numLocals
      · rw [if_pos hB] at h; cases h
      · rw [if_neg hB] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hLoanFresh : st.loanIdHwm ≤ loan := Nat.not_lt.mp hHwm
        have hLoanIdFresh : Ω.loanIdFresh loan := by
          subst hRep
          simpa [LLBCState.loanIdFresh, Concretise.concretise] using hLoanFresh
        have hSymValIdFresh : Ω.symValIdFresh symval := by
          subst hRep
          simp [LLBCState.symValIdFresh, Concretise.concretise]
        refine ⟨((Ω.setLocal place.local_ (.mutLoan loan)).bumpLoanId loan).bumpSymValId symval,
                ⟨hLoanIdFresh, hSymValIdFresh⟩,
                LStep.mutBorrow_loopOwned hLoanIdFresh hSymValIdFresh, ?_⟩
        simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
          LLBCState.bumpSymValId,
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

/-- M10.x.9 / C13' — `EvEndBorrow` with `.lazyExpand` loan kind, leak
    case: no env local holds the `mutLoan loan` token (either the cert
    omits `holderLocal` and `findHolder` returns `none`, or
    `holderLocal` points to a slot whose contents have been
    overwritten). The replayer's `stepEndBorrow` `.direct |
    .lazyExpand` arm returns `stTake` unchanged in this case (the
    "leak" branch); the paper side picks `LStep.endBorrow_reborrow`,
    whose post-state is `Ω` (no `LoanKind` constraint — the paper rule
    is naming-misleading but operationally just "post = Ω"). -/
theorem stepEndBorrow_leak_sound
  (hRep : concretise st = Ω)
  (loan : Nat) (restore : RestoreInfo) (stTake : SymState)
  (hTake : ∃ li : LoanInfo,
    st.takeLoan loan = some (li, stTake) ∧ li.kind = .lazyExpand)
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

    M10.x.4 — both Phase-D-dischargeable hypotheses
    (`hChildFresh : st.loanIdHwm ≤ child`,
     `hParentInHwm : parent < st.loanIdHwm`) drop:
    * `hChildFresh` is discharged from `hStep` via M10.x.2's
      monotone-allocator reject path.
    * `hParentInHwm` is replaced by a paper-side rule split: the
      tracked-parent branch (`st.loans.contains parent`) fires
      `LStep.reborrow` with post-state `Ω.bumpLoanId child`; the
      untracked-parent branch fires `LStep.reborrow_untracked` with
      post-state `(Ω.bumpLoanId parent).bumpLoanId child`, mirroring
      the replayer's `(st.addLoan parent _ _).addLoan child _ _`
      pre-add fallback. -/
theorem stepReborrow_sound
  (hRep : concretise st = Ω)
  (child parent : Nat) (place : Place)
  (parentLive : Bool) (parentAbs : Option Nat) :
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
    -- Guard 2 (M10.x.2): on success, `¬ st.loanIdHwm > child`.
    by_cases hHwm : st.loanIdHwm > child
    · rw [if_pos hHwm] at hStep; cases hStep
    · rw [if_neg hHwm] at hStep
      -- Guard 3: place's root local is in bounds.
      by_cases hB : place.local_ ≥ st.numLocals
      · rw [if_pos hB] at hStep; cases hStep
      · rw [if_neg hB] at hStep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
        subst hStep
        have hChildFresh : st.loanIdHwm ≤ child := Nat.not_lt.mp hHwm
        -- Paper-side freshness on the child id.
        have hChildIdFresh : Ω.loanIdFresh child := by
          subst hRep
          simpa [LLBCState.loanIdFresh, Concretise.concretise] using hChildFresh
        -- Dispatch on whether the parent loan is tracked. The
        -- tracked branch picks `LStep.reborrow`; the untracked
        -- branch picks `LStep.reborrow_untracked` (M10.x.4
        -- paper-side rule split).
        by_cases hP : st.loans.contains parent = true
        · rw [if_pos hP]
          refine ⟨Ω.bumpLoanId child,
                  hChildIdFresh,
                  LStep.reborrow hChildIdFresh, ?_⟩
          simp only [show (concretise : SymState → LLBCState)
                              = Concretise.concretise from rfl,
            Concretise.concretise_addLoan, hRep]
        · rw [if_neg hP]
          refine ⟨(Ω.bumpLoanId parent).bumpLoanId child,
                  hChildIdFresh,
                  LStep.reborrow_untracked hChildIdFresh, ?_⟩
          simp only [show (concretise : SymState → LLBCState)
                              = Concretise.concretise from rfl,
            Concretise.concretise_addLoan, hRep]

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

`stepEndAbs` (M10.x.6 refactor) factors as
`stepEndAbsValidate ; stepEndAbsBody`. On success the validation
returns `()`; the body deterministically computes the post-state via
three folds: `loansEraseIfPresent` (concretise-no-op),
`tokenClearOne` on env (paper-mirrored by `clearMutLoanToken`), and
`removeAbsShape`.

The paper-side `LStep.endAbs` post-state was strengthened in M10.x.6
to include the token-clear fold (replacing the previous vestigial
`Ω.abs abs = some r` premise + bare `Ω.removeAbs abs` post-state):
without it, the two sides genuinely diverge on fixtures whose env
holds `.mutLoan b` tokens for `b ∈ releasedLoans` (the replayer
clears them, the paper rule didn't). -/

/-- M10.x.6 — pull `concretise` through `stepEndAbsBody` as a fold of
    paper-side `clearMutLoanToken` over `(concretise st).removeAbs absId`.
    Chains three commutes: `removeAbsShape` ↦ `removeAbs`; env-fold
    mirror; loan-erase fold = concretise-no-op. -/
private theorem concretise_stepEndAbsBody_eq
    (st : SymState) (absId : Nat) (released tokenClearLocals : Array Nat) :
    concretise
        (AeneasCheck.LLBCSharp.stepEndAbsBody st absId released tokenClearLocals) =
      tokenClearLocals.foldl (init := (concretise st).removeAbs absId)
        LLBCSharpPaper.LLBCState.clearMutLoanToken := by
  -- Stage 1: `removeAbsShape` ↦ `removeAbs`. Use simp to push past
  -- the let-bindings introduced by `stepEndAbsBody`'s body.
  simp only [AeneasCheck.LLBCSharp.stepEndAbsBody,
             Concretise.concretise_removeAbsShape,
             Concretise.concretise_env_foldl_tokenClearOne,
             Concretise.concretise_foldl_loansEraseIfPresent]
  -- Goal: `(foldl clearMutLoanToken (concretise st) tokenClearLocals).removeAbs absId
  --      = foldl clearMutLoanToken ((concretise st).removeAbs absId) tokenClearLocals`.
  exact Concretise.foldl_clearMutLoanToken_removeAbs_commute
          (concretise st) absId tokenClearLocals

/-- C16 / M10.2p (M10.x.6 revision) — `EvEndAbs absId finalValues
    released tokenClearLocals` triggers `Reorg-End-Abs` (paper Fig. 8).
    No Phase-D hypotheses after M10.x.6: the `(shape, hAbsInRegistry,
    stPre, hConcPre, hShape)` triple is replaced by direct inversion
    of the replayer's `stepEndAbsValidate >>= stepEndAbsBody` factor
    plus the M10.x.6 commute lemmas in `Concretise/Lemmas.lean`. -/
theorem stepEndAbs_sound
  (hRep : concretise st = Ω)
  (absId : Nat) (finalValues : Array SymExpr) (releasedLoans : Array Nat)
  (tokenClearLocals : Array Nat) :
  stepEvent st (.endAbs absId finalValues releasedLoans tokenClearLocals) = .ok st' →
  ∃ Ω', Valid (.endAbs absId finalValues releasedLoans tokenClearLocals) Ω ∧
        LStep Ω (.endAbs absId finalValues releasedLoans tokenClearLocals) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Unfold the replayer body into `validate >>= body`.
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepEndAbs, bind, Except.bind,
    pure, Except.pure] at hStep
  -- Extract `st' = stepEndAbsBody …`. The validation result is
  -- `.ok ()` (success) or `.error _` (failure); only `.ok ()`
  -- continues to `return body`. Both branches reduce by `cases`
  -- on the validation result.
  set v := AeneasCheck.LLBCSharp.stepEndAbsValidate st absId releasedLoans
    with hv
  cases hVal : v with
  | error e =>
    rw [hVal] at hStep
    cases hStep
  | ok u =>
    rw [hVal] at hStep
    simp only [Except.ok.injEq] at hStep
    subst hStep
    -- Now `st' = stepEndAbsBody st absId releasedLoans tokenClearLocals`.
    -- Build the paper-side witness and chain the commute lemma.
    refine ⟨tokenClearLocals.foldl (init := Ω.removeAbs absId)
              LLBCSharpPaper.LLBCState.clearMutLoanToken,
            trivial,
            LStep.endAbs,
            ?_⟩
    -- The body-level commute lemma does the whole chain.
    rw [concretise_stepEndAbsBody_eq, ← hRep]

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

/-- M10.x.8 — `concretise` chain for the deterministic body of
    `stepSymExpandMutBorrow` (after the two guard checks succeed).
    The body is `addLoan bid .. .lazyExpand` applied to a record
    update whose env-field is `substLocals.foldl substLocalsOne ...`
    and whose loans-field is `substLoans.foldl substLoansOne ...`.
    Chains: addLoan ↦ bumpLoanId; substLoans-fold is concretise-no-op;
    substLocals-fold mirrors `substLocalOne` on the paper side. -/
private theorem concretise_stepSymExpandMutBorrowBody_eq
    (st : SymState) (svId bid innerSv : Nat)
    (substLocals substLoans : Array Nat) :
    let envFinal := substLocals.foldl
      (init := st.env) (AeneasCheck.LLBCSharp.substLocalsOne svId bid)
    let loansFinal := substLoans.foldl
      (init := st.loans) (AeneasCheck.LLBCSharp.substLoansOne svId bid)
    concretise ((({ st with env := envFinal, loans := loansFinal } :
        SymState)).addLoan bid (.sym innerSv) .lazyExpand) =
      ((substLocals.foldl (init := concretise st)
          (LLBCSharpPaper.LLBCState.substLocalOne svId bid)).bumpLoanId bid).bumpSymValId innerSv := by
  -- Strategy: peel off `addLoan` via `concretise_addLoan`; then split the
  -- env-substLocals fold and loans-substLoans fold via their respective
  -- commute lemmas.
  intro envFinal loansFinal
  -- Bridge the file-local abbrev `concretise` to `Concretise.concretise`
  -- (the abbrev otherwise blocks `rw [Concretise.concretise_addLoan]`).
  simp only [show (concretise : SymState → LLBCState) = Concretise.concretise from rfl,
             LLBCSharpPaper.LLBCState.bumpSymValId,
             Concretise.concretise_addLoan]
  -- Goal: (Concretise.concretise { st with env := envFinal, loans := loansFinal }).bumpLoanId bid
  --     = (foldl substLocalOne (Concretise.concretise st) substLocals).bumpLoanId bid
  congr 1
  -- Loans-update is invisible to concretise.
  have hLoansDrop :
      Concretise.concretise ({ st with env := envFinal, loans := loansFinal } : SymState)
        = Concretise.concretise ({ st with env := envFinal } : SymState) := by
    unfold Concretise.concretise; rfl
  rw [hLoansDrop]
  -- Env-fold via M10.x.8 mirror.
  exact Concretise.concretise_env_substLocalsOne_foldl st svId bid substLocals

/-- C17 / M10.x.8 revision — `EvSymExpandMutBorrow` (paper §4.1
    lazy expansion) with the substitution fold honestly modelled.
    M10.x.8 dropped all four hypotheses of the previous lemma:
    `hSubstLocalsEmpty`/`hSubstLoansEmpty` (replaced by paper-rule
    strengthening); `hBidNotInLoans` (replayer-discharged via
    `if st.loans.contains bid then fail`); `hBidFresh` (replayer-
    discharged via the M10.x.8 HWM reject path). -/
theorem stepSymExpandMutBorrow_sound
  (hRep : concretise st = Ω)
  (svId bid innerSv : Nat) (parentAbs : Option Nat)
  (substLocals substLoans : Array Nat) :
  stepEvent st
    (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) = .ok st' →
  ∃ Ω', Valid (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) Ω ∧
        LStep Ω (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Replayer body inversion: guards (loans, HWM) followed by substLocals/
  -- substLoans folds followed by addLoan.
  simp only [stepEvent, AeneasCheck.LLBCSharp.stepSymExpandMutBorrow] at hStep
  by_cases hC : st.loans.contains bid = true
  · rw [if_pos hC] at hStep; cases hStep
  · rw [if_neg hC] at hStep
    by_cases hHwm : st.loanIdHwm > bid
    · rw [if_pos hHwm] at hStep; cases hStep
    · rw [if_neg hHwm] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      have hBidFresh : st.loanIdHwm ≤ bid := Nat.not_lt.mp hHwm
      have hLoanIdFresh : Ω.loanIdFresh bid := by
        subst hRep
        simpa [LLBCState.loanIdFresh, Concretise.concretise] using hBidFresh
      have hSymValIdFresh : Ω.symValIdFresh innerSv := by
        subst hRep
        simp [LLBCState.symValIdFresh, Concretise.concretise]
      refine ⟨((substLocals.foldl (init := Ω)
                  (LLBCSharpPaper.LLBCState.substLocalOne svId bid)).bumpLoanId bid).bumpSymValId innerSv,
              ⟨hLoanIdFresh, hSymValIdFresh⟩,
              LStep.symExpandMutBorrow hLoanIdFresh hSymValIdFresh,
              ?_⟩
      -- Chain: concretise (env-foldl, loans-foldl, addLoan) =
      --   ((concretise st).substLocalsFold bid).bumpLoanId bid.
      -- substLoans is concretise-no-op; substLocals has its mirror;
      -- addLoan = bumpLoanId; bumpSymValId is no-op.
      -- Goal needs a normalised LHS; use the `concretise_stepSymExpandMutBorrowBody_eq`
      -- auxiliary.
      rw [concretise_stepSymExpandMutBorrowBody_eq, ← hRep]

/-! ### LoopInv (C24 / M10.3a — empty-loanRegistry subset)

The plan §3.2 row for C17 originally specified `stepLoopInv_sound`;
the campaign substituted `stepSymExpandMutBorrow` and deferred the
loop-fixpoint event lemma until Phase D needed it. We close it here
as part of M10.3a (Phase D's prep work) so the `stepEvent_sound`
case-split has a delegate for the `.loopInv` arm.

The replayer's `stepLoopInv` registers each entry of `loanRegistry`
as a fresh `.reborrow` loan if it isn't already in `st.loans`. The
paper-side `LStep.loopInv` is `Ω → Ω` (state unchanged at this
layer; the loop's region-abstraction surfaces via the surrounding
`EvCall` / `EvMutBorrow.loopOwned` events). The two coincide iff the
cert's `loanRegistry` is empty — i.e., every loan the loop's input
abstractions name was already registered by a prior event. Cert
v4-and-below emits non-empty `loanRegistry` only when the OCaml
side identifies an input borrow not already in scope; the M10
fixture set is empty-only. The full case awaits an M9.8-style
schema follow-up (extend `LStep.loopInv` to allow `.reborrow`-only
loan additions, or split into a `loopRegisterLoan` event). -/

/-- C24 / M10.3a (M10.x.7 revision) — `EvLoopInv loopId invariant
    loanRegistry` (paper §5.2 fixpoint snapshot). M10.x.7 dropped
    `CertGen_faithful.loopInv`'s `loanRegistry = #[]` hypothesis;
    instead the paper-side `LStep.loopInv` post-state was
    strengthened to a `loanRegistry.foldl bumpLoanId` (which the
    M10.x.7 commute lemma matches against the replayer's
    conditional `addLoan` fold). The lemma takes `HwmInvariant st`
    as an extra hypothesis (the skip-branch in the commute requires
    `b ∈ st.loans → b < st.loanIdHwm`). -/
theorem stepLoopInv_sound
  (hRep : concretise st = Ω)
  (hInv : Invariants.HwmInvariant st)
  (loopId : Nat) (invariant : StateSummary)
  (loanRegistry : Array (Nat × Nat)) :
  stepEvent st (.loopInv loopId invariant loanRegistry) = .ok st' →
  ∃ Ω', Valid (.loopInv loopId invariant loanRegistry) Ω ∧
        LStep Ω (.loopInv loopId invariant loanRegistry) Ω' ∧
        concretise st' = Ω' := by
  intro hStep
  -- Replayer body: `return loanRegistry.foldl loopInvRegisterLoan st`.
  simp only [stepEvent, Pure.pure, Except.pure, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨loanRegistry.foldl (init := Ω)
            (fun Ω' entry => Ω'.bumpLoanId entry.1),
          trivial,
          LStep.loopInv,
          ?_⟩
  have := Concretise.concretise_loopInvRegisterLoan_foldl hInv loanRegistry
  rw [← hRep]
  exact this

/-! ### Join (C23, general case — M10.2t)

`stepJoin st left right result witnesses` performs a wholesale
replacement: `newEnv := result.env.foldl (init := st.env) …`,
`prunedLoans := …` against `result.liveLoans`, and (M9.8) installs
each `joinMutBorrows _ _ _ absShape` witness's `absShape` in
`absRegistry` via `addAbsShape`. The paper-side `LStep.join` instead
chains per-entry `JoinEntryStep` rules via
`JoinChain Ω witnesses.toList Ω'`.

M9.8 closed the structural "fresh abs" gap: the cert's
`JrJoinMutBorrows.abs` is now a full `AbsShape`, the replayer's
`stepJoin` installs it in `absRegistry`, and the paper-side
`JoinEntryStep.mutBorrows` lifts the same shape via `liftAbsShape`.
What remains for C23 is the per-entry / wholesale-replace shape
correspondence: the replayer doesn't compute the chain's
intermediate states, so building `JoinChain Ω witnesses.toList Ω'`
and proving `concretise st' = Ω'` requires data the cert names
indirectly (each entry's freshness premises and the matching of
`result.env` / `result.liveLoans` against the chain's terminal).
Both are CertGen_faithful obligations dispatched in Phase D.

The lemma's signature lifts these obligations to explicit
parameters (`Ω'` the chain terminal, `hChain` the chain proof,
`hConcMatch` the correspondence) — mirroring the
`(stPre, hConcPre, hShape)` triple pattern used by C11-C13 and
C16. Phase D's `stepEvent_sound` constructs the chain by induction
on `witnesses.toList` and applies the matching
`JoinLemmas.join<Rule>_step` helper per entry, threading the
freshness premises from `CertGen_faithful`. The
`concretise st' = Ω'` discharge then comes from
`CertGen_faithful`'s structural promise that the cert's
`result.env` / `result.liveLoans` exactly mirror the chain's
terminal env / live loans (and the abs-installation in `stepJoin`
matches the chain's `setAbs` operations by construction).

The empty-witnesses subset that M10.2s closed is now a trivial
corollary (`witnesses = #[]` => `chain = JoinChain.nil` =>
`Ω' = Ω`); kept as `stepJoin_witnessed_sound_empty` below for
regression-anchoring. -/

/-- C23 / M10.2t — `EvJoin { witnesses }` soundness, general case.
    The chain terminal `Ω'` and the chain `hChain` are explicit
    inputs; Phase D builds them by induction over `witnesses.toList`
    via the per-entry `JoinLemmas.join<Rule>_step` helpers. The
    correspondence `hConcMatch : concretise st' = Ω'` is also
    Phase-D-dispatched from `CertGen_faithful`'s promise about
    `result.env` / `result.liveLoans` shape. -/
theorem stepJoin_witnessed_sound
  (left right result : StateSummary) (witnesses : Array JoinEntry)
  (_hRep : concretise st = Ω)
  (Ω' : LLBCState)
  (hChain : LLBCSharpPaper.JoinChain Ω witnesses.toList Ω')
  (hConcMatch : concretise st' = Ω') :
  stepEvent st (.join left right result witnesses) = .ok st' →
  ∃ Ω', Valid (.join left right result witnesses) Ω ∧
        LStep Ω (.join left right result witnesses) Ω' ∧
        concretise st' = Ω' := by
  intro _hStep
  -- `_hRep` and `_hStep` are unused in the body because the chain
  -- terminal `Ω'` and the correspondence `hConcMatch` are provided
  -- directly; they're kept in the signature for parity with the
  -- other C-lemmas (Phase D's case dispatch threads `hRep` /
  -- `hStep` to every per-event lemma uniformly).
  exact ⟨Ω', ⟨Ω', hChain⟩, LStep.join hChain, hConcMatch⟩

/-- C23 corollary — `EvJoin` with empty `witnesses` (the M10.2s
    case). The chain is `JoinChain.nil`, terminal `Ω' = Ω`, and the
    correspondence reduces to `concretise st' = concretise st` —
    Phase-D-dischargeable in the no-witness case from
    `CertGen_faithful`'s promise that the wholesale replace at
    `result.env` / `result.liveLoans` is concretise-preserving when
    every cert-entry resolved to identity. Kept as a regression
    anchor so the empty case is named separately. -/
theorem stepJoin_witnessed_sound_empty
  (left right result : StateSummary) (witnesses : Array JoinEntry)
  (hRep : concretise st = Ω)
  (hWitnessesEmpty : witnesses = #[])
  (hStShape : concretise st' = concretise st) :
  stepEvent st (.join left right result witnesses) = .ok st' →
  ∃ Ω', Valid (.join left right result witnesses) Ω ∧
        LStep Ω (.join left right result witnesses) Ω' ∧
        concretise st' = Ω' := by
  intro _hStep
  subst hWitnessesEmpty
  refine ⟨Ω, ⟨Ω, LLBCSharpPaper.JoinChain.nil⟩, LStep.join LLBCSharpPaper.JoinChain.nil, ?_⟩
  exact hStShape.trans hRep

end StepEvent

/-! ## Top-level: `stepEvent_sound`

Case-analysis on `ev`. Hint-bearing events sub-case on the hint and
delegate to the per-rule lemma above; non-hinted events apply their
single-rule lemma directly. Closed by Phase-D M10.3a (which assembles
the per-event lemmas added across Phase C). -/

theorem stepEvent_sound :
    ∀ (ev : Event) (st st' : SymState) (Ω : LLBCState),
      concretise st = Ω →
      Invariants.HwmInvariant st →
      stepEvent st ev = .ok st' →
      ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ concretise st' = Ω' := by
  intro ev st st' Ω hRep hInv hStep
  cases ev with
  | mutBorrow loan place symval kindHint =>
    cases kindHint with
    | direct =>
      -- M10.x.4: `CertGen_faithful.mutBorrow_direct` retired; the
      -- per-event lemma reads the HWM-fresh + projection-tolerant
      -- post-state directly from `hStep`.
      exact stepMutBorrow_direct_sound st st' Ω hRep loan place symval hStep
    | inAbsReborrow absId =>
      -- M10.x.5: `CertGen_faithful.mutBorrow_inAbsReborrow` retired.
      -- The `∃ r, Ω.abs absId = some r` premise was vestigial in the
      -- paper rule; the HWM clause is replayer-discharged via
      -- M10.x.2's `stepMutBorrow` monotone-allocator reject path.
      exact stepMutBorrow_inAbsReborrow_sound st st' Ω hRep loan place symval absId hStep
    | loopOwned loopId =>
      -- M10.x.4: `CertGen_faithful.mutBorrow_loopOwned` retired.
      exact stepMutBorrow_loopOwned_sound st st' Ω hRep loan place symval loopId hStep
  | sharedBorrow loan sbId place symval =>
    -- M10.x.4: `CertGen_faithful.sharedBorrow` retired.
    exact stepSharedBorrow_sound st st' Ω hRep loan sbId place symval hStep
  | assign dst rhs =>
    exact stepAssign_sound st st' Ω hRep dst rhs hStep
  | move src dst =>
    -- M10.x.3: `move` was a `CertGen_faithful` extractor; the per-event
    -- lemma now mirrors the replayer's root-local semantics directly
    -- via `resolvePlaceRoot`, so no extractor call is needed.
    exact stepMove_sound st st' Ω hRep src dst hStep
  | copy src dst =>
    -- M10.x.3: same as `move`.
    exact stepCopy_sound st st' Ω hRep src dst hStep
  | endBorrow loan restore =>
    -- M10.4a-post: `endBorrow_takeOk` was a hStep-derivable extractor; replaced
    -- by direct inversion through the replayer's `stepEndBorrow`-on-`none` fail.
    obtain ⟨li, stTake, hTakeRaw⟩ : ∃ li stTake, st.takeLoan loan = some (li, stTake) := by
      match h : st.takeLoan loan with
      | none =>
        exfalso
        simp [stepEvent, stepEndBorrow, h] at hStep
        injection hStep
      | some (li, stTake) => exact ⟨li, stTake, rfl⟩
    -- Dispatch by the replayer's `LoanKind`.
    cases hKind : li.kind with
    | direct =>
      -- M10.x.9: `endBorrow_direct_witness` retired. Invert hStep through
      -- evalSymExpr, the holderOpt dispatch, and the env[x] / b = loan
      -- check. `.direct` rejects every non-success path via `.error`, so
      -- hStep's `.ok` forces the success-branch shape and extracts
      -- `(x, v, env[x]? = some (.mutLoan loan))`.
      have hStep' := hStep
      simp only [stepEvent, stepEndBorrow, hTakeRaw, hKind, bind, Except.bind] at hStep'
      match hEval : evalSymExpr stTake restore.givenBack with
      | .error _ => rw [hEval] at hStep'; cases hStep'
      | .ok v =>
        rw [hEval] at hStep'
        simp only [] at hStep'
        match hHo : restore.holderLocal.orElse (fun () => findHolder stTake loan) with
        | none =>
          rw [hHo] at hStep'; simp only [] at hStep'; cases hStep'
        | some x =>
          rw [hHo] at hStep'
          simp only [] at hStep'
          match hLk : stTake.env[x]? with
          | none =>
            rw [hLk] at hStep'; simp only [] at hStep'; cases hStep'
          | some .bottom =>
            rw [hLk] at hStep'; simp only [] at hStep'; cases hStep'
          | some (.sym _) =>
            rw [hLk] at hStep'; simp only [] at hStep'; cases hStep'
          | some (.lit _) =>
            rw [hLk] at hStep'; simp only [] at hStep'; cases hStep'
          | some (.mutBorrow _ _) =>
            rw [hLk] at hStep'; simp only [] at hStep'; cases hStep'
          | some (.mutLoan b) =>
            rw [hLk] at hStep'
            simp only [] at hStep'
            by_cases hb : b = loan
            · -- Success path: b = loan; st' = { stTake with env := env.insert x v }.
              rw [hb] at hLk hStep'
              simp only [if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
              have hShape : stepEvent st (.endBorrow loan restore) =
                            .ok (stTake.setLocal x v) := by
                rw [hStep, ← hStep']; rfl
              have hHolder : Ω.ctx x = some (.mutLoan loan) := by
                have hConc : concretise stTake = concretise st :=
                  Concretise.concretise_takeLoan _ _ hTakeRaw
                rw [← hRep, ← hConc]
                show (concretise stTake).ctx x = some (.mutLoan loan)
                rw [Concretise.concretise_ctx_apply, hLk]; rfl
              exact stepEndBorrow_direct_sound st st' Ω hRep loan restore x v stTake
                ⟨li, hTakeRaw, Or.inl hKind⟩ hHolder hShape hStep
            · -- b ≠ loan + .direct: replayer's "else fail" branch fires.
              simp only [hb, if_false, Pure.pure, Except.pure] at hStep'
              cases hStep'
    | lazyExpand =>
      -- M10.x.9: same inversion as `.direct`, but the leak-branch
      -- (no-holder / env-mismatch) also yields `.ok stTake`; route those
      -- to `stepEndBorrow_leak_sound`.
      have hStep' := hStep
      simp only [stepEvent, stepEndBorrow, hTakeRaw, hKind, bind, Except.bind] at hStep'
      match hEval : evalSymExpr stTake restore.givenBack with
      | .error _ => rw [hEval] at hStep'; cases hStep'
      | .ok v =>
        rw [hEval] at hStep'
        simp only [] at hStep'
        -- Helper for the leak-branch: discharge via stepEndBorrow_leak_sound.
        have leakDispatch : st' = stTake →
            ∃ Ω', Valid (.endBorrow loan restore) Ω ∧
                  LStep Ω (.endBorrow loan restore) Ω' ∧
                  concretise st' = Ω' := by
          intro hStEq
          have hShape : stepEvent st (.endBorrow loan restore) = .ok stTake := by
            rw [hStep, hStEq]
          exact stepEndBorrow_leak_sound st st' Ω hRep loan restore stTake
            ⟨li, hTakeRaw, hKind⟩ hShape hStep
        match hHo : restore.holderLocal.orElse (fun () => findHolder stTake loan) with
        | none =>
          rw [hHo] at hStep'
          simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
            if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
          exact leakDispatch hStep'.symm
        | some x =>
          rw [hHo] at hStep'
          simp only [] at hStep'
          match hLk : stTake.env[x]? with
          | none =>
            rw [hLk] at hStep'
            simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
              if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
            exact leakDispatch hStep'.symm
          | some .bottom =>
            rw [hLk] at hStep'
            simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
              if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
            exact leakDispatch hStep'.symm
          | some (.sym _) =>
            rw [hLk] at hStep'
            simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
              if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
            exact leakDispatch hStep'.symm
          | some (.lit _) =>
            rw [hLk] at hStep'
            simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
              if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
            exact leakDispatch hStep'.symm
          | some (.mutBorrow _ _) =>
            rw [hLk] at hStep'
            simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
              if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
            exact leakDispatch hStep'.symm
          | some (.mutLoan b) =>
            rw [hLk] at hStep'
            simp only [] at hStep'
            by_cases hb : b = loan
            · -- Success path: same as the `.direct` success arm.
              rw [hb] at hLk hStep'
              simp only [if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
              have hShape : stepEvent st (.endBorrow loan restore) =
                            .ok (stTake.setLocal x v) := by
                rw [hStep, ← hStep']; rfl
              have hHolder : Ω.ctx x = some (.mutLoan loan) := by
                have hConc : concretise stTake = concretise st :=
                  Concretise.concretise_takeLoan _ _ hTakeRaw
                rw [← hRep, ← hConc]
                show (concretise stTake).ctx x = some (.mutLoan loan)
                rw [Concretise.concretise_ctx_apply, hLk]; rfl
              exact stepEndBorrow_direct_sound st st' Ω hRep loan restore x v stTake
                ⟨li, hTakeRaw, Or.inr hKind⟩ hHolder hShape hStep
            · -- b ≠ loan: leak (lazyExpand-only).
              simp only [hb, if_false,
                show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep'
              exact leakDispatch hStep'.symm
    | reborrow =>
      -- M10.4a-post: `endBorrow_reborrow_witness` was hStep-derivable; the
      -- replayer's `.reborrow` arm runs `evalSymExpr` then returns `stTake`,
      -- so `hStep` forces `st' = stTake`.
      have hShape : stepEvent st (.endBorrow loan restore) = .ok stTake := by
        have hStep' := hStep
        simp only [stepEvent, stepEndBorrow, hTakeRaw, hKind] at hStep'
        cases hEval : evalSymExpr stTake restore.givenBack with
        | error e => rw [hEval] at hStep'; simp at hStep'
        | ok v => rw [hEval] at hStep'; simp at hStep'; subst hStep'; exact hStep
      exact stepEndBorrow_reborrow_sound st st' Ω hRep loan restore stTake
        ⟨li, hTakeRaw, hKind⟩ hShape hStep
    | shared =>
      -- M10.4a-post: `endBorrow_shared_witness` was hStep-derivable, same
      -- shape as the `.reborrow` arm above.
      have hShape : stepEvent st (.endBorrow loan restore) = .ok stTake := by
        have hStep' := hStep
        simp only [stepEvent, stepEndBorrow, hTakeRaw, hKind] at hStep'
        cases hEval : evalSymExpr stTake restore.givenBack with
        | error e => rw [hEval] at hStep'; simp at hStep'
        | ok v => rw [hEval] at hStep'; simp at hStep'; subst hStep'; exact hStep
      exact stepEndBorrow_shared_sound st st' Ω hRep loan restore stTake
        ⟨li, hTakeRaw, hKind⟩ hShape hStep
  | assert cond expected =>
    exact stepAssert_sound st st' Ω hRep cond expected hStep
  | panic =>
    exact stepPanic_sound st st' Ω hRep hStep
  | retn =>
    exact stepRetn_sound st st' Ω hRep hStep
  | binop op lhs rhs dst =>
    exact stepBinop_sound st st' Ω hRep op lhs rhs dst hStep
  | reborrow child parent place parentLive parentAbs =>
    -- M10.x.4: `CertGen_faithful.reborrow` retired. The HWM-fresh
    -- child clause is replayer-discharged via M10.x.2's reject path;
    -- the parent-in-HWM clause is replaced by a paper-side rule
    -- split (`LStep.reborrow` vs `LStep.reborrow_untracked`).
    exact stepReborrow_sound st st' Ω hRep child parent place parentLive parentAbs hStep
  | call fn callId fnName args dst regionAbs absSig =>
    -- M10.4a-post: `CertGen_faithful.call` (dst-in-bounds) was hStep-derivable;
    -- the replayer's `stepCall` fails on `root ≥ numLocals`, so the inequality
    -- falls out by inverting through that fail-path.
    have hDstInBounds : dst.local_ < st.numLocals := by
      by_contra h
      simp [stepEvent, stepCall, placeRootLocal, Nat.not_lt.mp h] at hStep
      injection hStep
    exact stepCall_sound st st' Ω hRep fn callId fnName args dst regionAbs absSig
      hDstInBounds hStep
  | endAbs absId finalValues releasedLoans tokenClearLocals =>
    -- M10.x.6: `CertGen_faithful.endAbs` retired. The previous
    -- (shape, hAbsInRegistry, stPre, hConcPre, hShape) bundle is
    -- replaced by the `stepEndAbsValidate`/`stepEndAbsBody` factor
    -- + M10.x.6 commute lemmas; the per-event lemma now takes only
    -- `hRep` and `hStep`.
    exact stepEndAbs_sound st st' Ω hRep absId finalValues releasedLoans tokenClearLocals
      hStep
  | proj absId p sv =>
    -- The replayer rejects `.proj` events with `.error`; `hStep`'s
    -- `.error _ = .ok st'` is a contradiction. (`Valid (.proj _ _ _)
    -- = False` on the paper side; this dispatch keeps the two in
    -- sync — a cert that ever emits `EvProj` is rejected by both.)
    simp [stepEvent] at hStep
  | symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans =>
    -- M10.x.8: `CertGen_faithful.symExpandMutBorrow` retired. The
    -- paper-side rule's post-state was strengthened with a substLocals
    -- fold; hBidNotInLoans / hBidFresh are replayer-discharged via
    -- guard + M10.x.8 HWM reject.
    exact stepSymExpandMutBorrow_sound st st' Ω hRep svId bid innerSv parentAbs
      substLocals substLoans hStep
  | join left right result witnesses =>
    obtain ⟨Ω', hChain, hConcMatch⟩ :=
      CertGen_faithful.join st st' left right result witnesses Ω hRep hStep
    exact stepJoin_witnessed_sound st st' Ω left right result witnesses hRep Ω'
      hChain hConcMatch hStep
  | loopInv loopId invariant loanRegistry =>
    -- M10.x.7: `CertGen_faithful.loopInv` retired. The paper-side
    -- `LStep.loopInv` post-state was strengthened to a
    -- `loanRegistry.foldl bumpLoanId`; the per-event lemma now
    -- consumes the M10.x.1 `HwmInvariant` plumbing.
    exact stepLoopInv_sound st st' Ω hRep hInv loopId invariant loanRegistry hStep
  | loopEnd loopId =>
    exact stepLoopEnd_sound st st' Ω hRep loopId hStep
  | matchArm scrutinee adtId variantId variantName =>
    exact stepMatchArm_sound st st' Ω hRep scrutinee adtId variantId variantName hStep

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
