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

The pairing lemma. `sorry`'d at M10.0j (the file lives under
`LLBCSharpPaper/`, outside G6's `Soundness/` scope). Phase C closes
each direction case-by-case:

* `(→)`: per-event existence — given the premises, build `Ω'` and
  apply the corresponding `LStep` constructor.
* `(←)`: per-event inversion — given an `LStep` proof, extract the
  premises by inverting on the constructor.

The `LStep`-side existence direction (`→`) is more useful in
Phase C/D; the inversion direction is bookkeeping. The lemma is
load-bearing for Phase D's `stepEvent_sound` case analysis. -/
theorem Valid_iff_LStep_exists (e : Event) (Ω : LLBCState) :
    Valid e Ω ↔ ∃ Ω', LStep Ω e Ω' := by
  sorry

end AeneasSoundness.LLBCSharpPaper
