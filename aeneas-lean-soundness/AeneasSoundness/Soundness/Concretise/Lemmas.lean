import AeneasSoundness.Soundness.Concretise.Defn
import AeneasSoundness.Soundness.Invariants.HWM

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
open AeneasSoundness.Soundness.Invariants (HwmInvariant LoanHwmInvariant)

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

/-- Paper-side counterpart of `SymState.addAbsShape`: install one
    shape via `setAbs` + `bumpAbsId`. Named so the M10.0m
    `LStep.call` post-state and the M10.2o-revised C15 proof can
    refer to it by name. -/
def installAbsShapePaper (Ω : LLBCState) (shape : AbsShape) : LLBCState :=
  (Ω.setAbs shape.absId (liftAbsShape shape)).bumpAbsId shape.absId

/-- Fold-style commute lemma for `addAbsShape`: pushing `concretise`
    through `absSig.foldl SymState.addAbsShape` reduces to
    `absSig.foldl installAbsShapePaper (concretise st)`. Used by
    M10.2o-revised C15 to discharge the `concretise st' = Ω'`
    conjunct over the full (non-empty) absSig case. -/
theorem concretise_foldl_addAbsShape (st : SymState) (absSig : Array AbsShape) :
    concretise (absSig.foldl SymState.addAbsShape st) =
      absSig.foldl installAbsShapePaper (concretise st) := by
  -- Convert both Array.foldls to List.foldls over absSig.toList.
  rw [show absSig.foldl SymState.addAbsShape st
        = absSig.toList.foldl SymState.addAbsShape st from by simp [Array.foldl_toList],
      show absSig.foldl installAbsShapePaper (concretise st)
        = absSig.toList.foldl installAbsShapePaper (concretise st) from
          by simp [Array.foldl_toList]]
  induction absSig.toList generalizing st with
  | nil => rfl
  | cons shape rest ih =>
    simp only [List.foldl_cons]
    rw [ih (st.addAbsShape shape), concretise_addAbsShape]
    rfl

/-! ## M10.x.6 (endAbs preamble)

The replayer's `stepEndAbs` body is a three-phase fold:

1. `released.foldl loansEraseIfPresent` — erases each loan id from
   `st.loans`. `concretise` doesn't read `loans` (loans live inside
   `ctx` as `mutLoan` tokens; the separate `loans` map is a replayer-
   only bookkeeping field), so this is a `concretise`-no-op.
2. `tokenClearLocals.foldl tokenClearOne` — rewrites `env[l]?` from
   `some (.mutLoan _)` to `some .bottom` (other shapes left alone).
   This DOES change `concretise.ctx`; the paper-side mirror is the
   `clearMutLoanToken` fold on `LLBCState`.
3. `removeAbsShape absId` — closed by the existing
   `concretise_removeAbsShape`. -/

/-- `loansEraseIfPresent` is a `concretise`-no-op: erasing a loan id
    from `st.loans` doesn't touch `env`, `absRegistry`, or either HWM,
    and `concretise` only reads those four fields. -/
theorem concretise_loansEraseIfPresent (st : SymState) (b : Nat) :
    concretise (AeneasCheck.LLBCSharp.loansEraseIfPresent st b) =
      concretise st := by
  unfold AeneasCheck.LLBCSharp.loansEraseIfPresent
  split
  · rfl
  · rfl

/-- Fold-style: the entire `released.foldl loansEraseIfPresent` is a
    `concretise`-no-op. -/
theorem concretise_foldl_loansEraseIfPresent (st : SymState)
    (released : Array Nat) :
    concretise
        (released.foldl (init := st) AeneasCheck.LLBCSharp.loansEraseIfPresent) =
      concretise st := by
  rw [show released.foldl (init := st) AeneasCheck.LLBCSharp.loansEraseIfPresent
        = released.toList.foldl AeneasCheck.LLBCSharp.loansEraseIfPresent st from by
          simp [Array.foldl_toList]]
  induction released.toList generalizing st with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.foldl_cons]
    rw [ih (AeneasCheck.LLBCSharp.loansEraseIfPresent st b),
        concretise_loansEraseIfPresent]

/-- Per-step token-clear commute: the replayer's `tokenClearOne` on
    `st.env` mirrors the paper-side `clearMutLoanToken` on
    `concretise st`. The case analysis matches arm-for-arm; the
    `some (.mutLoan _)` arm uses `concretise_setLocal` plus
    `liftVal .bottom = .bottom`. -/
theorem concretise_env_tokenClearOne (st : SymState) (l : Nat) :
    concretise { st with env := AeneasCheck.LLBCSharp.tokenClearOne st.env l } =
      LLBCSharpPaper.LLBCState.clearMutLoanToken (concretise st) l := by
  unfold AeneasCheck.LLBCSharp.tokenClearOne LLBCSharpPaper.LLBCState.clearMutLoanToken
  -- The replayer matches on `env[l]?`; the paper-side matches on
  -- `concretise.ctx l = (env[l]?).map liftVal`. The cases align
  -- because `liftVal` preserves the `.mutLoan` constructor.
  have hCtx : (concretise st).ctx l = (st.env[l]?).map liftVal := by
    unfold concretise liftEnv; rfl
  rw [hCtx]
  cases hLook : st.env[l]? with
  | none =>
    -- replayer: env unchanged; paper: ctx l = none → no change.
    simp
  | some v =>
    cases v with
    | mutLoan b =>
      -- replayer: env.insert l .bottom; paper: setLocal l .bottom.
      simp only [liftVal, Option.map_some]
      -- Goal: concretise { st with env := st.env.insert l .bottom }
      --     = (concretise st).setLocal l .bottom
      have : ({ st with env := st.env.insert l .bottom } : SymState)
            = st.setLocal l .bottom := rfl
      rw [this, concretise_setLocal]
      rfl
    | sym _ => rfl  -- non-mutLoan: both sides leave state alone
    | lit _ => rfl
    | mutBorrow _ _ => rfl
    | bottom => rfl

/-- Auxiliary fold-style commute over a list and a free env-start.
    Reformulated to put the env-start under the inductive forall so
    the cons-step `ih` recovers the right shape. -/
private theorem concretise_env_foldl_tokenClearOne_aux
    (st : SymState) :
    ∀ (xs : List Nat) (env₀ : Std.HashMap Nat AeneasCheck.LLBCSharp.Val),
      concretise ({ st with
            env := xs.foldl AeneasCheck.LLBCSharp.tokenClearOne env₀ } : SymState)
        = xs.foldl LLBCSharpPaper.LLBCState.clearMutLoanToken
            (concretise ({ st with env := env₀ } : SymState))
  | [], env₀ => by simp
  | l :: rest, env₀ => by
      simp only [List.foldl_cons]
      have hIH := concretise_env_foldl_tokenClearOne_aux st rest
                    (AeneasCheck.LLBCSharp.tokenClearOne env₀ l)
      rw [hIH]
      congr 1
      -- Per-step commute on the auxiliary `{ st with env := env₀ }`.
      have := concretise_env_tokenClearOne
                ({ st with env := env₀ } : SymState) l
      simpa using this

/-- Fold-style: the `tokenClearLocals` fold on the replayer's env
    mirrors the `clearMutLoanToken` fold on the paper-side state. -/
theorem concretise_env_foldl_tokenClearOne (st : SymState)
    (tokenClearLocals : Array Nat) :
    let envFinal := tokenClearLocals.foldl
        (init := st.env) AeneasCheck.LLBCSharp.tokenClearOne
    concretise ({ st with env := envFinal } : SymState) =
      tokenClearLocals.foldl (init := concretise st)
        LLBCSharpPaper.LLBCState.clearMutLoanToken := by
  have := concretise_env_foldl_tokenClearOne_aux st
            tokenClearLocals.toList st.env
  simp only [Array.foldl_toList] at this
  exact this

/-- Paper-side commute: `clearMutLoanToken` (which only updates `ctx`)
    commutes with `removeAbs` (which only updates `abs`). Used by
    `stepEndAbs_sound` to align the order of operations in the
    paper-rule's post-state with the replayer's. -/
theorem clearMutLoanToken_removeAbs_commute (Ω : LLBCSharpPaper.LLBCState)
    (abs : Nat) (l : Nat) :
    (Ω.removeAbs abs).clearMutLoanToken l =
      (Ω.clearMutLoanToken l).removeAbs abs := by
  unfold LLBCSharpPaper.LLBCState.clearMutLoanToken LLBCSharpPaper.LLBCState.removeAbs
    LLBCSharpPaper.LLBCState.setLocal
  -- The match scrutinee `(Ω.removeAbs abs).ctx l` is definitionally
  -- the same as `Ω.ctx l` because removeAbs only updates `abs`.
  show (match Ω.ctx l with
        | some (.mutLoan _) => _ | _ => _) = _
  cases h : Ω.ctx l with
  | none => rfl
  | some v =>
    -- Both sides update `ctx` (only on `mutLoan _`) and `abs`; since
    -- the two updates target distinct fields the order is irrelevant
    -- and `rfl` closes regardless of which `Val` arm we're in.
    cases v <;> rfl

/-- Foldl-version: `tokenClearLocals.foldl clearMutLoanToken` commutes
    with `removeAbs abs` over any starting state. -/
theorem foldl_clearMutLoanToken_removeAbs_commute (Ω : LLBCSharpPaper.LLBCState)
    (abs : Nat) (tokenClearLocals : Array Nat) :
    (tokenClearLocals.foldl (init := Ω) LLBCSharpPaper.LLBCState.clearMutLoanToken).removeAbs abs =
      tokenClearLocals.foldl (init := Ω.removeAbs abs)
        LLBCSharpPaper.LLBCState.clearMutLoanToken := by
  rw [show tokenClearLocals.foldl (init := Ω) LLBCSharpPaper.LLBCState.clearMutLoanToken
        = tokenClearLocals.toList.foldl LLBCSharpPaper.LLBCState.clearMutLoanToken Ω from by
        simp [Array.foldl_toList],
      show tokenClearLocals.foldl (init := Ω.removeAbs abs)
            LLBCSharpPaper.LLBCState.clearMutLoanToken
        = tokenClearLocals.toList.foldl LLBCSharpPaper.LLBCState.clearMutLoanToken
            (Ω.removeAbs abs) from by simp [Array.foldl_toList]]
  induction tokenClearLocals.toList generalizing Ω with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl_cons]
    rw [ih (Ω.clearMutLoanToken l), clearMutLoanToken_removeAbs_commute]

/-! ## M10.x.7 (loopInv loanRegistry fold)

The replayer's `stepLoopInv` runs
`loanRegistry.foldl loopInvRegisterLoan st` — conditionally
adding a `.reborrow` loan when `entry.1 ∉ st.loans`. The paper-side
`LStep.loopInv` post-state mirrors with an unconditional
`bumpLoanId entry.1` fold. The two coincide at the `concretise`
level under the `HwmInvariant` assumption: when the replayer's
skip-branch fires (`b ∈ st.loans`), the invariant says
`b < st.loanIdHwm`, so `(concretise st).bumpLoanId b` is idempotent
(`max nextLoanId (b+1) = nextLoanId`). The paper-side unconditional
bump therefore matches the replayer's skip-branch as well as its
add-branch. -/

/-- Per-entry commute for `loopInv` (under `LoanHwmInvariant`):
    registering one entry on the replayer side is `bumpLoanId entry.1`
    on the paper side. The add-branch closes via `concretise_addLoan`;
    the skip-branch closes via the LoanHwmInvariant's `loanBound` (the
    skipped `b` is `< st.loanIdHwm`, so the paper-side `bumpLoanId b`
    is a no-op on `nextLoanId`).

    M10.x.11: takes `LoanHwmInvariant` (the strictly weaker loan-half
    of the bundled `HwmInvariant`). The `absBound` clause is irrelevant
    to this commute; splitting it out lets Phase E preserve the loan
    half across the four shape-leaking events (`join`, `endBorrow`,
    `endAbs`, `symExpandMutBorrow`) without an `eventRespectsHwm`
    structural promise. -/
theorem concretise_loopInvRegisterLoan {st : SymState}
    (hInv : LoanHwmInvariant st) (entry : Nat × Nat) :
    concretise (AeneasCheck.LLBCSharp.loopInvRegisterLoan st entry) =
      (concretise st).bumpLoanId entry.1 := by
  unfold AeneasCheck.LLBCSharp.loopInvRegisterLoan
  obtain ⟨b, _parentAbs⟩ := entry
  by_cases hC : st.loans.contains b = true
  · -- skip-branch.
    simp only [hC, if_true]
    -- Goal: concretise st = (concretise st).bumpLoanId b.
    -- Paper `bumpLoanId b` is `nextLoanId := max nextLoanId (b+1)`.
    -- `concretise st.nextLoanId = st.loanIdHwm`. By `hInv.loanBound`,
    -- `b < st.loanIdHwm`, hence `max st.loanIdHwm (b+1) = st.loanIdHwm`.
    unfold concretise LLBCSharpPaper.LLBCState.bumpLoanId
    have hBound : b < st.loanIdHwm := hInv.loanBound b hC
    refine LLBCSharpPaper.LLBCState.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_⟩
    refine LLBCSharpPaper.NonceCounters.mk.injEq .. |>.mpr ⟨?_, rfl, rfl⟩
    -- nextLoanId.new = max st.loanIdHwm (b+1) = st.loanIdHwm.
    exact (Nat.max_eq_left hBound).symm
  · -- add-branch.
    simp only [hC, if_false]
    exact concretise_addLoan st b .bottom .reborrow

/-- Auxiliary fold-style commute (LoanHwmInvariant-threaded over the list). -/
private theorem concretise_loopInvRegisterLoan_foldl_aux
    : ∀ (xs : List (Nat × Nat)) {st : SymState},
      LoanHwmInvariant st →
        concretise (xs.foldl AeneasCheck.LLBCSharp.loopInvRegisterLoan st)
        = xs.foldl
            (fun Ω' entry => Ω'.bumpLoanId entry.1)
            (concretise st)
  | [], _, _ => rfl
  | entry :: rest, st, hInv => by
    simp only [List.foldl_cons]
    -- LoanHwmInvariant is preserved by `loopInvRegisterLoan`.
    have hInv' : LoanHwmInvariant
        (AeneasCheck.LLBCSharp.loopInvRegisterLoan st entry) :=
      Invariants.loopInvRegisterLoan_preserves_LoanHwm hInv entry
    have hIH := concretise_loopInvRegisterLoan_foldl_aux rest hInv'
    rw [hIH, concretise_loopInvRegisterLoan hInv entry]

/-- Fold commute for `loopInv`: under `LoanHwmInvariant`, the replayer's
    `loanRegistry.foldl loopInvRegisterLoan` matches the paper-side
    fold of unconditional `bumpLoanId`. -/
theorem concretise_loopInvRegisterLoan_foldl {st : SymState}
    (hInv : LoanHwmInvariant st) (loanRegistry : Array (Nat × Nat)) :
    concretise
        (loanRegistry.foldl (init := st)
          AeneasCheck.LLBCSharp.loopInvRegisterLoan) =
      loanRegistry.foldl (init := concretise st)
        (fun Ω' entry => Ω'.bumpLoanId entry.1) := by
  rw [show loanRegistry.foldl (init := st)
              AeneasCheck.LLBCSharp.loopInvRegisterLoan
          = loanRegistry.toList.foldl
              AeneasCheck.LLBCSharp.loopInvRegisterLoan st from by
        simp [Array.foldl_toList],
      show loanRegistry.foldl (init := concretise st)
              (fun Ω' entry => Ω'.bumpLoanId entry.1)
          = loanRegistry.toList.foldl
              (fun Ω' entry => Ω'.bumpLoanId entry.1) (concretise st) from by
        simp [Array.foldl_toList]]
  exact concretise_loopInvRegisterLoan_foldl_aux loanRegistry.toList hInv

/-! ## M10.x.8 (symExpandMutBorrow substitution folds)

The replayer's `stepSymExpandMutBorrow` body unconditionally folds
`substLocalsOne svId bid` over `substLocals` (the env half) and
`substLoansOne svId bid` over `substLoans` (the loans half), then
calls `addLoan bid (.sym innerSv) .lazyExpand`. The substLoans
half is concretise-no-op (`concretise` does not read `loans`);
substLocals has a paper-side mirror via
`LLBCState.substLocalOne`. -/

/-- Per-step env-rewrite commute: the replayer's `substLocalsOne`
    matches paper-side `substLocalOne`. Case analysis on `env[l]?`
    runs arm-for-arm with `liftVal`'s preservation of `.sym` and
    insertion of `.mutLoan bid`. -/
theorem concretise_env_substLocalsOne
    (st : SymState) (svId bid l : Nat) :
    concretise ({ st with env :=
      AeneasCheck.LLBCSharp.substLocalsOne svId bid st.env l } : SymState) =
      LLBCSharpPaper.LLBCState.substLocalOne svId bid (concretise st) l := by
  unfold AeneasCheck.LLBCSharp.substLocalsOne LLBCSharpPaper.LLBCState.substLocalOne
  have hCtx : (concretise st).ctx l = (st.env[l]?).map liftVal := by
    unfold concretise liftEnv; rfl
  rw [hCtx]
  cases hLook : st.env[l]? with
  | none => simp
  | some v =>
    cases v with
    | sym k =>
      simp only [Option.map_some, liftVal]
      by_cases hK : k = svId
      · subst hK
        simp only [if_true]
        have hEta : ({ st with env := st.env.insert l (.mutLoan bid) } : SymState)
            = st.setLocal l (.mutLoan bid) := rfl
        rw [hEta, concretise_setLocal]
        rfl
      · simp [hK]
    | mutLoan _ => rfl
    | lit _ => rfl
    | mutBorrow _ _ => rfl
    | bottom => rfl

/-- Auxiliary list-fold version of the substLocals env-rewrite commute. -/
private theorem concretise_env_substLocalsOne_foldl_aux (st : SymState)
    (svId bid : Nat) :
    ∀ (xs : List Nat) (env₀ : Std.HashMap Nat AeneasCheck.LLBCSharp.Val),
      concretise ({ st with
        env := xs.foldl
          (AeneasCheck.LLBCSharp.substLocalsOne svId bid) env₀ } : SymState)
      = xs.foldl
          (LLBCSharpPaper.LLBCState.substLocalOne svId bid)
          (concretise ({ st with env := env₀ } : SymState))
  | [], _ => rfl
  | l :: rest, env₀ => by
      simp only [List.foldl_cons]
      have hIH := concretise_env_substLocalsOne_foldl_aux st svId bid rest
                    (AeneasCheck.LLBCSharp.substLocalsOne svId bid env₀ l)
      rw [hIH]
      congr 1
      have := concretise_env_substLocalsOne
                ({ st with env := env₀ } : SymState) svId bid l
      simpa using this

/-- Fold-style env-rewrite commute for substLocals. -/
theorem concretise_env_substLocalsOne_foldl (st : SymState)
    (svId bid : Nat) (substLocals : Array Nat) :
    let envFinal := substLocals.foldl
      (init := st.env) (AeneasCheck.LLBCSharp.substLocalsOne svId bid)
    concretise ({ st with env := envFinal } : SymState) =
      substLocals.foldl (init := concretise st)
        (LLBCSharpPaper.LLBCState.substLocalOne svId bid) := by
  have := concretise_env_substLocalsOne_foldl_aux st svId bid
            substLocals.toList st.env
  simp only [Array.foldl_toList] at this
  exact this

/-- The substLoans fold is concretise-no-op: only `st.loans` changes,
    and `concretise` doesn't read `loans`. -/
theorem concretise_loans_substLoansOne (st : SymState) (svId bid b : Nat) :
    concretise ({ st with loans :=
      AeneasCheck.LLBCSharp.substLoansOne svId bid st.loans b } : SymState) =
      concretise st := by
  unfold AeneasCheck.LLBCSharp.substLoansOne
  split
  · split
    · split
      · rfl
      · rfl
    · rfl
  · rfl

/-- Auxiliary list-fold no-op (substLoans). -/
private theorem concretise_loans_substLoansOne_foldl_aux (st : SymState)
    (svId bid : Nat) :
    ∀ (xs : List Nat)
      (loans₀ : Std.HashMap Nat AeneasCheck.LLBCSharp.LoanInfo),
      concretise ({ st with
        loans := xs.foldl
          (AeneasCheck.LLBCSharp.substLoansOne svId bid) loans₀ } : SymState)
      = concretise ({ st with loans := loans₀ } : SymState)
  | [], _ => rfl
  | b :: rest, loans₀ => by
      simp only [List.foldl_cons]
      have hIH := concretise_loans_substLoansOne_foldl_aux st svId bid rest
                    (AeneasCheck.LLBCSharp.substLoansOne svId bid loans₀ b)
      rw [hIH]
      -- Per-step: concretise insensitive to loans changes.
      unfold AeneasCheck.LLBCSharp.substLoansOne
      split <;> [(split <;> [(split <;> rfl); rfl]); rfl]

/-- Fold-form of `concretise_loans_substLoansOne`. -/
theorem concretise_loans_substLoansOne_foldl (st : SymState)
    (svId bid : Nat) (substLoans : Array Nat) :
    let loansFinal := substLoans.foldl
      (init := st.loans) (AeneasCheck.LLBCSharp.substLoansOne svId bid)
    concretise ({ st with loans := loansFinal } : SymState) =
      concretise st := by
  have h := concretise_loans_substLoansOne_foldl_aux st svId bid
              substLoans.toList st.loans
  simp only [Array.foldl_toList] at h
  have hEta : ({ st with loans := st.loans } : SymState) = st := rfl
  rw [hEta] at h
  exact h

end AeneasSoundness.Soundness.Concretise
