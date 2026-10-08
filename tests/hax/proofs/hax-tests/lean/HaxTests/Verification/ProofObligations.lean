-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
import Aeneas
import CoreModels
import HaxTests.Extraction.Types
import HaxTests.Extraction.Funs
import HaxTests.Extraction.Specs
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

set_option maxHeartbeats 1000000

set_option maxRecDepth 2048

noncomputable section

namespace hax_tests

theorem basic.only_requires.spec.proof (x : Std.U32) :
  basic.only_requires.spec x
  := by
  unfold basic.only_requires.spec basic.only_requires
  hax_mvcgen
  scalar_tac

theorem basic.only_ensures.spec.proof (x : Std.U32) : basic.only_ensures.spec x
  := by
  unfold basic.only_ensures.spec basic.only_ensures
  hax_mvcgen
  simp

theorem basic.both.spec.proof (x : Std.U32) : basic.both.spec x := by
  unfold basic.both.spec basic.both
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac

theorem basic.no_args.spec.proof : basic.no_args.spec := by
  unfold basic.no_args.spec basic.no_args
  hax_mvcgen

theorem basic.returns_unit.spec.proof (x : Std.U32) : basic.returns_unit.spec x
  := by
  unfold basic.returns_unit.spec basic.returns_unit
  hax_mvcgen

theorem basic.block_in_requires.spec.proof (x : Std.U32) :
  basic.block_in_requires.spec x
  := by
  unfold basic.block_in_requires.spec basic.block_in_requires
  hax_mvcgen

theorem basic.returns_pair.spec.proof (x : Std.U32) : basic.returns_pair.spec x
  := by
  unfold basic.returns_pair.spec basic.returns_pair
  hax_mvcgen
  simp

theorem extra_args.generic.spec.proof (N : Std.U32) (x : Std.U32) :
  extra_args.generic.spec N x
  := by
  unfold extra_args.generic.spec extra_args.generic
  hax_mvcgen [extra_args.generic.pre, extra_args.generic.post]
  · simp; scalar_tac
  · scalar_tac

theorem extra_args.traits.spec.proof {T : Type} (ValInst : extra_args.Val T)
  (t : T) (x : Std.U32) : extra_args.traits.spec ValInst t x
  := by
  unfold extra_args.traits.spec extra_args.traits
  intro h
  unfold extra_args.traits.pre at h
  cases hv : ValInst.value t
  · rw [hv] at h
    hax_mvcgen [extra_args.traits.post]
    · simp; scalar_tac
    · scalar_tac
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem future.incr.spec.proof (x : Std.U32) : future.incr.spec x := by
  unfold future.incr.spec future.incr
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem future.incr_i.spec.proof (x : Slice Std.U32) (i : Std.Usize) :
  future.incr_i.spec x i
  := by
  unfold future.incr_i.spec future.incr_i
  hax_mvcgen [future.incr_i.pre, future.incr_i.post, core.slice.Slice.len]
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac
  · simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac

theorem future.swap_and_add.spec.proof (x : Std.U32) (y : Std.U32) :
  future.swap_and_add.spec x y
  := by
  unfold future.swap_and_add.spec future.swap_and_add
  hax_mvcgen [future.swap_and_add.pre, future.swap_and_add.post]
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem implicit_generics.nothing.spec.proof (T : Type) (k : Std.Usize) :
  implicit_generics.nothing.spec T k
  := by
  unfold implicit_generics.nothing.spec implicit_generics.nothing
  hax_mvcgen

theorem implicit_generics.of_fst.spec.proof {T : Type} (N : Std.Usize) 
  (t : T) : implicit_generics.of_fst.spec N t
  := by
  unfold implicit_generics.of_fst.spec implicit_generics.of_fst
  hax_mvcgen

theorem implicit_generics.empty.spec.proof (T : Type) (N : Std.Usize)
  (k : Std.Usize) : implicit_generics.empty.spec T N k
  := by
  unfold implicit_generics.empty.spec implicit_generics.empty
  hax_mvcgen

theorem unit_args.named.spec.proof (_ : Unit) : unit_args.named.spec ()
  := by
  unfold unit_args.named.spec unit_args.named
  hax_mvcgen

theorem unit_args.before_other.spec.proof (_ : Unit) (y : Std.U32) :
  unit_args.before_other.spec () y
  := by
  unfold unit_args.before_other.spec unit_args.before_other
  hax_mvcgen
  simp

theorem reserved_names.foo.spec.proof (x : Std.U32) : reserved_names.foo.spec x
  := by
  unfold reserved_names.foo.spec reserved_names.foo
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem const_generic_ty.MyStruct.build.spec.proof (N : Std.Usize)
  (k : Std.Usize) : const_generic_ty.MyStruct.build.spec N k
  := by
  unfold const_generic_ty.MyStruct.build.spec const_generic_ty.MyStruct.build
  hax_mvcgen

theorem const_generic_ty.MyStruct.get.spec.proof {N : Std.Usize}
  (self : const_generic_ty.MyStruct N) :
  const_generic_ty.MyStruct.get.spec self
  := by
  unfold const_generic_ty.MyStruct.get.spec const_generic_ty.MyStruct.get
  hax_mvcgen

theorem Tuple.Insts.Hax_testsUnit_argsSize.len.spec.proof (_ : Unit) :
  Tuple.Insts.Hax_testsUnit_argsSize.len.spec ()
  := by
  unfold Tuple.Insts.Hax_testsUnit_argsSize.len.spec Tuple.Insts.Hax_testsUnit_argsSize.len
  hax_mvcgen

theorem
  supertraits.B.provided.default.spec.proof {Self : Type} (BInst :
                                           supertraits.B Self) (self : Self) :
  supertraits.B.provided.default.spec BInst self
  := by
  unfold supertraits.B.provided.default.spec supertraits.B.provided.default
  intro h
  unfold supertraits.B.provided.pre at h
  cases hv : BInst.AInst.a self
  · rw [hv] at h
    hax_mvcgen [supertraits.B.provided.post, hv]
    simp
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem
  supertraits.C.provided_c.default.spec.proof {Self : Type} (CInst :
                                             supertraits.C Self) (self : Self)
  : supertraits.C.provided_c.default.spec CInst self
  := by
  unfold supertraits.C.provided_c.default.spec supertraits.C.provided_c.default
  intro h
  unfold supertraits.C.provided_c.pre at h
  cases hv : CInst.BInst.AInst.a self
  · rw [hv] at h
    hax_mvcgen [supertraits.C.provided_c.post, hv]
    simp
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

/-- `is_even` and `is_odd` call each other: their triples are proved together,
by induction on `n`. -/
theorem mutual.triples (k : Nat) (n : Std.U32) (h : n.val = k) :
    ⦃ ⌜ True ⌝ ⦄ mutual.is_even n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 0) ⌝ ⦄ ∧
    ⦃ ⌜ True ⌝ ⦄ mutual.is_odd n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 1) ⌝ ⦄ := by
  induction k generalizing n with
  | zero =>
    constructor
    · rw [mutual.is_even]
      hax_mvcgen
      · agrind
      · exfalso; scalar_tac
      · exfalso; scalar_tac
    · rw [mutual.is_odd]
      hax_mvcgen
      · agrind
      · exfalso; scalar_tac
      · exfalso; scalar_tac
  | succ k ih =>
    constructor
    · rw [mutual.is_even]
      hax_mvcgen
      · exfalso; scalar_tac
      · next r _ _ =>
        have := (ih r (by scalar_tac)).2
        mvcgen [this]
        simp_all only [decide_eq_decide]
        scalar_tac
      · exfalso; scalar_tac
    · rw [mutual.is_odd]
      hax_mvcgen
      · exfalso; scalar_tac
      · next r _ _ =>
        have := (ih r (by scalar_tac)).1
        mvcgen [this]
        simp_all only [decide_eq_decide]
        scalar_tac
      · exfalso; scalar_tac

@[spec]
theorem mutual.is_even.triple (n : Std.U32) :
  ⦃ ⌜ True ⌝ ⦄ mutual.is_even n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 0) ⌝ ⦄ :=
  (mutual.triples _ n rfl).1

theorem mutual.is_even.spec.proof (n : Std.U32) :
  mutual.is_even.spec n
  := by
  unfold mutual.is_even.spec
  hax_mvcgen [mutual.is_even.pre, mutual.is_even.post]
  agrind

@[spec]
theorem mutual.is_odd.triple (n : Std.U32) :
  ⦃ ⌜ True ⌝ ⦄ mutual.is_odd n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 1) ⌝ ⦄ :=
  (mutual.triples _ n rfl).2

theorem mutual.is_odd.spec.proof (n : Std.U32) :
  mutual.is_odd.spec n
  := by
  unfold mutual.is_odd.spec
  hax_mvcgen [mutual.is_odd.pre, mutual.is_odd.post]
  agrind

end hax_tests
