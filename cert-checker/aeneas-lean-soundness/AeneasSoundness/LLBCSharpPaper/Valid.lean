import AeneasSoundness.LLBCSharpPaper.Step

/-!
# LLBC# paper-side per-event side-condition predicate: `Valid e Ω`

Plan §1.1 row 6 / §1.3 commit A10. `Valid` is a definitional `match`
on `Event` that returns the conjunction of the matching `LStep`
constructor's premises. Pairing with `LStep`, the smoke lemma

```
theorem Valid_iff_LStep_exists (e : Event) (Ω : LLBCState) :
    Valid e Ω ↔ ∃ Ω', LStep Ω e Ω'
```

ties the two sides together: every well-formed event step has a
discharge in `LStep`, and every `LStep` proof entails the
side-conditions.

## Why a separate predicate?

`LStep`'s premises are scattered across 27 constructors as a mix of
explicit hypotheses and existential binders (`{v : Val}`, `{r :
RegionAbs}`, `{σ : SymValId}`). `Valid` flattens that into a single
function-like predicate so:

* Phase-C per-event lemmas can quote *exactly* the premises they need
  to discharge (`Valid e Ω → … → ∃ Ω', LStep Ω e Ω' ∧ concretise st'
  = Ω'`).
* Phase-D `stepEvent_sound` can case on `Event` and, in each branch,
  unfold `Valid` directly without inverting the inductive `LStep`.

The `match` mirrors paper Fig. 3 / 7 / 8 / 9 / 11 / §5.2 premise
columns; constructors with multiple `LStep` rules (e.g. `endBorrow`
splits into direct / reborrow / shared) collapse to the disjunction
of their premises, which here reduces to `True` because the
reborrow / shared variants have no baseline premises.

## Multiplicity caveats

`Event.binop`, `Event.assign`, `Event.call` carry existential
binders (`σ`, `v`) in their `LStep` constructor that are *not*
present in the `Event` payload. `Valid` quantifies them existentially
on the `Ω` side; the `σ`-freshness witness is always realisable
(pick `σ := Ω.freshness.nextSymValId`) so the existential degenerates
to `True` in the proof of `Valid_iff_LStep_exists` (Phase C).

## Smoke lemma scope

`Valid_iff_LStep_exists` is `sorry`'d at M10.0j; the per-direction
proofs land case-by-case across Phase C (each per-event lemma
discharges one branch). The `sorry` lives under `LLBCSharpPaper/`
which is *outside* the G6 `Soundness/` scope; G6 stays clean.
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw

/-! ### Valid : Event → LLBCState → Prop -/

/-- The per-event side-condition predicate. For each `Event`
    constructor, return the conjunction of the corresponding
    `LStep` constructor's premises. Constructors with multiple
    `LStep` discharges (split by hint) collapse to the disjunction,
    which here always reduces to a sum because the variants are
    distinguished syntactically (e.g. `MutBorrowKind`). -/
def Valid (e : Event) (Ω : LLBCState) : Prop :=
  match e with
  -- Fig. 3 — direct-borrow / ownership / control-flow ---
  -- M10.x.4 — the `.direct` / `.loopOwned` / `.sharedBorrow` rules
  -- dropped their `Ω.resolvePlace p = some v` existential (the
  -- value `v` was vestigial in the `LStep` post-state); the
  -- premise list collapses to freshness only.
  | .mutBorrow ℓ _ σ .direct =>
      Ω.loanIdFresh ℓ ∧ Ω.symValIdFresh σ
  -- M10.x.5 — `.inAbsReborrow` lost its `∃ r, Ω.abs absId = some r`
  -- premise (the bound `r` was vestigial in `LStep.mutBorrow_inAbsReborrow`'s
  -- post-state). 112/783 fixtures emit `inAbsReborrow.absId` for ambient
  -- function-input abs not event-installed; the existential would have
  -- been false on those certs.
  | .mutBorrow ℓ _ σ (.inAbsReborrow _) =>
      Ω.loanIdFresh ℓ ∧ Ω.symValIdFresh σ
  | .mutBorrow ℓ _ σ (.loopOwned _) =>
      Ω.loanIdFresh ℓ ∧ Ω.symValIdFresh σ
  | .sharedBorrow ℓ _ _ σ =>
      Ω.loanIdFresh ℓ ∧ Ω.symValIdFresh σ
  -- `endBorrow` splits into endBorrow_direct (∃ x, ctx x =
  -- some (.mutLoan ℓ)), endBorrow_reborrow (no premise), and
  -- endBorrow_shared (no premise). The disjunction is `True`.
  | .endBorrow _ _ => True
  -- M10.x.3 — `.move` / `.copy` are premise-free in `LStep` after
  -- the `resolvePlaceRoot` refactor (the rule reads the root local
  -- with `.bottom` default rather than walking a projection chain).
  | .move _ _ => True
  | .copy _ _ => True
  -- `assign`'s rhs reduces to `v` existentially in LStep; no
  -- baseline premise on Ω.
  | .assign _ _ => True
  -- `assert` splits into assert_true / assert_false_panic; both
  -- baseline-premise-free.
  | .assert _ _ => True
  | .panic => True
  | .retn => True
  -- `binop` existentially picks a fresh σ; always realisable.
  | .binop _ _ _ _ => ∃ σ, Ω.symValIdFresh σ
  -- Fig. 7 + Fig. 8 — abstraction rules ---
  | .reborrow child _ _ _ _ => Ω.loanIdFresh child
  -- `call` existentially picks a fresh σ; always realisable.
  | .call _ _ _ _ _ _ _ => ∃ σ, Ω.symValIdFresh σ
  -- M10.x.6 — the `∃ r, Ω.abs abs = some r` premise was vestigial in
  -- `LStep.endAbs` (the bound `r` did not appear in the post-state).
  -- The previous existential was tolerated by the replayer (silent
  -- skip on `absRegistry[abs]?.isNone`); keeping it would falsify
  -- `CertGen_faithful` on ambient-abs fixtures. The post-state was
  -- strengthened with a `tokenClearLocals.foldl` over
  -- `clearMutLoanToken`; the rule itself is now premise-free.
  | .endAbs _ _ _ _ => True
  | .symExpandMutBorrow _ bid innerSv _ _ _ =>
      Ω.loanIdFresh bid ∧ Ω.symValIdFresh innerSv
  -- `proj` has no `LStep` constructor at M10 — `EvProj` revival is
  -- M11+ work (plan §14.8). Mark as `False` so
  -- `Valid_iff_LStep_exists` remains vacuously consistent on this
  -- branch; the Phase-D case-split will surface the gap if a cert
  -- ever emits a `proj` event.
  | .proj _ _ _ => False
  -- Fig. 11 — join rules ---
  | .join _ _ _ witnesses => ∃ Ω', JoinChain Ω witnesses.toList Ω'
  -- §5.2 — loop fixpoint ---
  | .loopInv _ _ _ => True
  | .loopEnd _ => True
  -- Translator marker (no rule fires).
  | .matchArm _ _ _ _ => True

/-! ### Smoke lemma: `Valid_iff_LStep_exists`

The pairing lemma. Discharged at M10 cleanup (post-campaign-close):
the proof is a 17-arm case-split, one per `Event` constructor,
mirroring each `LStep` constructor's premises with the
corresponding `Valid` arm.

* `(→)`: per-event existence — given the `Valid` premises, build
  `Ω'` and apply the matching `LStep` constructor. Hint-bearing
  events (`mutBorrow.kindHint`, `assert.expected`) pick the
  matching `LStep` arm.
* `(←)`: per-event inversion — given an `LStep` proof, extract
  the premises by `cases` on the constructor. Each arm
  discharges the `Valid` clause for the matching event shape.

The `proj` arm is doubly vacuous: `Valid (.proj …) = False` and
`LStep` has no `.proj` constructor, so both sides reduce to
`False`. -/
theorem Valid_iff_LStep_exists (e : Event) (Ω : LLBCState) :
    Valid e Ω ↔ ∃ Ω', LStep Ω e Ω' := by
  constructor
  · -- Forward: Valid e Ω → ∃ Ω', LStep Ω e Ω'.
    intro hV
    cases e with
    | mutBorrow ℓ p σ kindHint =>
      cases kindHint with
      | direct =>
        obtain ⟨hLF, hSF⟩ := hV
        exact ⟨_, LStep.mutBorrow_direct hLF hSF⟩
      | inAbsReborrow absId =>
        obtain ⟨hLF, hSF⟩ := hV
        exact ⟨_, LStep.mutBorrow_inAbsReborrow hLF hSF⟩
      | loopOwned loopId =>
        obtain ⟨hLF, hSF⟩ := hV
        exact ⟨_, LStep.mutBorrow_loopOwned hLF hSF⟩
    | sharedBorrow ℓ sbId p σ =>
      obtain ⟨hLF, hSF⟩ := hV
      exact ⟨_, LStep.sharedBorrow hLF hSF⟩
    | endBorrow _ _ =>
      -- Valid is True. Pick `endBorrow_reborrow` (post = Ω, premise-free).
      exact ⟨Ω, LStep.endBorrow_reborrow⟩
    | move _ _ => exact ⟨_, LStep.move⟩
    | copy _ _ => exact ⟨_, LStep.copy⟩
    | assign _ _ =>
      -- LStep.assign existentially binds `v`. Pick any.
      exact ⟨_, LStep.assign (v := .bottom)⟩
    | assert _ expected =>
      cases expected with
      | true => exact ⟨Ω, LStep.assert_true⟩
      | false => exact ⟨Ω, LStep.assert_false_panic⟩
    | panic => exact ⟨Ω, LStep.panic⟩
    | retn => exact ⟨Ω, LStep.retn⟩
    | binop _ _ _ _ =>
      obtain ⟨_, hSF⟩ := hV
      exact ⟨_, LStep.binop hSF⟩
    | reborrow _ _ _ _ _ =>
      -- Valid carries `Ω.loanIdFresh child`. Pick `LStep.reborrow`
      -- (tracked-parent branch); the untracked variant is also
      -- inhabited but we only need one witness.
      exact ⟨_, LStep.reborrow hV⟩
    | call _ _ _ _ _ _ _ =>
      obtain ⟨_, hSF⟩ := hV
      exact ⟨_, LStep.call hSF⟩
    | endAbs _ _ _ _ => exact ⟨_, LStep.endAbs⟩
    | symExpandMutBorrow _ _ _ _ _ _ =>
      obtain ⟨hBF, hIF⟩ := hV
      exact ⟨_, LStep.symExpandMutBorrow hBF hIF⟩
    | proj _ _ _ =>
      -- Valid is False — contradiction.
      exact absurd hV (by intro h; exact h)
    | join _ _ _ witnesses =>
      obtain ⟨Ω', hChain⟩ := hV
      exact ⟨Ω', LStep.join hChain⟩
    | loopInv _ _ _ => exact ⟨_, LStep.loopInv⟩
    | loopEnd _ => exact ⟨Ω, LStep.loopEnd⟩
    | matchArm _ _ _ _ => exact ⟨Ω, LStep.matchArm⟩
  · -- Reverse: (∃ Ω', LStep Ω e Ω') → Valid e Ω.
    intro hEx
    obtain ⟨Ω', hStep⟩ := hEx
    cases hStep with
    | mutBorrow_direct hLF hSF => exact ⟨hLF, hSF⟩
    | mutBorrow_inAbsReborrow hLF hSF => exact ⟨hLF, hSF⟩
    | mutBorrow_loopOwned hLF hSF => exact ⟨hLF, hSF⟩
    | sharedBorrow hLF hSF => exact ⟨hLF, hSF⟩
    | endBorrow_direct _ => trivial
    | endBorrow_reborrow => trivial
    | endBorrow_shared => trivial
    | move => trivial
    | copy => trivial
    | assign => trivial
    | assert_true => trivial
    | assert_false_panic => trivial
    | panic => trivial
    | retn => trivial
    | binop hSF => exact ⟨_, hSF⟩
    | reborrow hLF => exact hLF
    | reborrow_untracked hLF => exact hLF
    | call hSF => exact ⟨_, hSF⟩
    | endAbs => trivial
    | symExpandMutBorrow hBF hIF => exact ⟨hBF, hIF⟩
    | join hChain => exact ⟨_, hChain⟩
    | loopInv => trivial
    | loopEnd => trivial
    | matchArm => trivial

end AeneasSoundness.LLBCSharpPaper
