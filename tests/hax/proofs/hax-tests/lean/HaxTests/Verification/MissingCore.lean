-- Lemmas about hax's core models (`CoreModels`) which are missing upstream.
-- Kept here until they are upstreamed to hax's Lean library.
import Aeneas
import CoreModels
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option mvcgen.warning false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section


namespace CoreModels

-- The blanket `Into` forwards to `From::from`.
@[spec] theorem core.convert.Into.Blanket.into_spec {T U : Type}
    (FromInst : core.convert.From U T) (self : T) {Q}
    (h : ⦃ ⌜ True ⌝ ⦄ FromInst.«from» self ⦃ Q ⦄) :
    ⦃ ⌜ True ⌝ ⦄ core.convert.Into.Blanket.into FromInst self ⦃ Q ⦄ := h

-- The reflexive `From<T> for T` is the identity.
@[spec] theorem core.convert.From.Blanket.from_spec {T : Type} (x : T) {Q}
    (h : PostCond.ok Q x) :
    ⦃ ⌜ True ⌝ ⦄ core.convert.From.Blanket.from x ⦃ Q ⦄ := by
  unfold core.convert.From.Blanket.from
  mvcgen

-- `<=` on mathematical integers (default `le` of the `PartialOrd` instance) is `Int.le`.
theorem core.cmp.PartialOrd.le.default.Int_eq (a b : hax_lib.int.Int) :
    core.cmp.PartialOrd.le.default hax_lib.int.Int.Insts.CoreCmpPartialOrdInt a b
      = ok (decide (a ≤ b)) := by
  simp only [core.cmp.PartialOrd.le.default, hax_lib.int.Int.Insts.CoreCmpPartialOrdInt]
  simp only [compare, compareOfLessAndEq]
  split_ifs <;> simp_all <;> agrind

-- `Range<u32>::next` (the `U32` analogue of the `I32`/`Usize` specs of
-- `Hax/Tactic/ForLoopWithInvariantSpec.lean`), and the cast facts it needs.
theorem U32_MAX_cast_usize_val :
    (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = 4294967295 := by
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])]
  simp [core.num.U32.MAX, U32.rMax]

theorem U32_MIN_cast_usize_val :
    (UScalar.cast UScalarTy.Usize core.num.U32.MIN).val = 0 := by
  simp [core.num.U32.MIN, UScalar.cast_val_eq]

theorem usize_one_cast_u32_val :
    (UScalar.cast UScalarTy.U32 1#usize).val = 1 := by
  simp [UScalar.cast_val_eq]

@[spec]
theorem core.IteratorRange_next_spec_u32 (i e : Std.U32) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.U32), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.U32.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next core.U32.Insts.CoreIterRangeStep
  by_cases h : i.val < e.val
  · simp_all [compare, compareOfLessAndEq,
      core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd,
      core.U32.Insts.CoreCloneClone.clone,
      core.U32.Insts.CoreIterRangeStep.forward_checked,
      core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
      core.num.U32.checked_add, core.num.U32.overflowing_add]
    mvcgen
    · agrind [U32_MAX_cast_usize_val, U32_MIN_cast_usize_val, usize_one_cast_u32_val,
      UScalar.overflowing_add_eq i (UScalar.cast .U32 1#usize)]
    · agrind [U32_MAX_cast_usize_val, U32_MIN_cast_usize_val, usize_one_cast_u32_val,
      UScalar.overflowing_add_eq i (UScalar.cast .U32 1#usize)]
    · agrind [U32_MAX_cast_usize_val, U32_MIN_cast_usize_val, usize_one_cast_u32_val,
      UScalar.overflowing_add_eq i (UScalar.cast .U32 1#usize)]
    · agrind [U32_MAX_cast_usize_val, U32_MIN_cast_usize_val, usize_one_cast_u32_val,
      UScalar.overflowing_add_eq i (UScalar.cast .U32 1#usize)]
  · have h_ge' := h_ge (Nat.le_of_not_lt h)
    simp_all [compare, compareOfLessAndEq, core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
    mvcgen
    agrind

end CoreModels
