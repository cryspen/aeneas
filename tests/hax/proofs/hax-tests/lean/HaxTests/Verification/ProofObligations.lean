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

theorem specs.contracts.only_requires.spec.proof (x : Std.U32) :
  specs.contracts.only_requires.spec x
  := by
  unfold specs.contracts.only_requires.spec specs.contracts.only_requires
  hax_mvcgen
  scalar_tac

theorem specs.contracts.only_ensures.spec.proof (x : Std.U32) : specs.contracts.only_ensures.spec x
  := by
  unfold specs.contracts.only_ensures.spec specs.contracts.only_ensures
  hax_mvcgen
  simp

theorem specs.contracts.both.spec.proof (x : Std.U32) : specs.contracts.both.spec x := by
  unfold specs.contracts.both.spec specs.contracts.both
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac

theorem specs.contracts.no_args.spec.proof : specs.contracts.no_args.spec := by
  unfold specs.contracts.no_args.spec specs.contracts.no_args
  hax_mvcgen

theorem specs.contracts.returns_unit.spec.proof (x : Std.U32) : specs.contracts.returns_unit.spec x
  := by
  unfold specs.contracts.returns_unit.spec specs.contracts.returns_unit
  hax_mvcgen

theorem specs.contracts.block_in_requires.spec.proof (x : Std.U32) :
  specs.contracts.block_in_requires.spec x
  := by
  unfold specs.contracts.block_in_requires.spec specs.contracts.block_in_requires
  hax_mvcgen

theorem specs.contracts.returns_pair.spec.proof (x : Std.U32) : specs.contracts.returns_pair.spec x
  := by
  unfold specs.contracts.returns_pair.spec specs.contracts.returns_pair
  hax_mvcgen
  simp

theorem specs.generics.generic.spec.proof (N : Std.U32) (x : Std.U32) :
  specs.generics.generic.spec N x
  := by
  unfold specs.generics.generic.spec specs.generics.generic
  hax_mvcgen [specs.generics.generic.pre, specs.generics.generic.post]
  · simp; scalar_tac
  · scalar_tac

theorem specs.generics.trait_clause.spec.proof {T : Type} (ValInst : specs.generics.Val T)
  (t : T) (x : Std.U32) : specs.generics.trait_clause.spec ValInst t x
  := by
  unfold specs.generics.trait_clause.spec specs.generics.trait_clause
  intro h
  unfold specs.generics.trait_clause.pre at h
  cases hv : ValInst.value t
  · rw [hv] at h
    hax_mvcgen [specs.generics.trait_clause.post]
    · simp; scalar_tac
    · scalar_tac
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem specs.mutable_borrows.incr.spec.proof (x : Std.U32) : specs.mutable_borrows.incr.spec x := by
  unfold specs.mutable_borrows.incr.spec specs.mutable_borrows.incr
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem specs.mutable_borrows.incr_i.spec.proof (x : Slice Std.U32) (i : Std.Usize) :
  specs.mutable_borrows.incr_i.spec x i
  := by
  unfold specs.mutable_borrows.incr_i.spec specs.mutable_borrows.incr_i
  hax_mvcgen [specs.mutable_borrows.incr_i.pre, specs.mutable_borrows.incr_i.post, core.slice.Slice.len]
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

theorem specs.mutable_borrows.swap_and_add.spec.proof (x : Std.U32) (y : Std.U32) :
  specs.mutable_borrows.swap_and_add.spec x y
  := by
  unfold specs.mutable_borrows.swap_and_add.spec specs.mutable_borrows.swap_and_add
  hax_mvcgen [specs.mutable_borrows.swap_and_add.pre, specs.mutable_borrows.swap_and_add.post]
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem specs.generics.nothing.spec.proof (T : Type) (k : Std.Usize) :
  specs.generics.nothing.spec T k
  := by
  unfold specs.generics.nothing.spec specs.generics.nothing
  hax_mvcgen

theorem specs.generics.of_fst.spec.proof {T : Type} (N : Std.Usize) 
  (t : T) : specs.generics.of_fst.spec N t
  := by
  unfold specs.generics.of_fst.spec specs.generics.of_fst
  hax_mvcgen

theorem specs.generics.empty.spec.proof (T : Type) (N : Std.Usize)
  (k : Std.Usize) : specs.generics.empty.spec T N k
  := by
  unfold specs.generics.empty.spec specs.generics.empty
  hax_mvcgen

theorem specs.arguments.named.spec.proof (_ : Unit) : specs.arguments.named.spec ()
  := by
  unfold specs.arguments.named.spec specs.arguments.named
  hax_mvcgen

theorem specs.arguments.before_other.spec.proof (_ : Unit) (y : Std.U32) :
  specs.arguments.before_other.spec () y
  := by
  unfold specs.arguments.before_other.spec specs.arguments.before_other
  hax_mvcgen
  simp

theorem specs.naming.foo.spec.proof (x : Std.U32) : specs.naming.foo.spec x
  := by
  unfold specs.naming.foo.spec specs.naming.foo
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem specs.generics.MyStruct.build.spec.proof (N : Std.Usize)
  (k : Std.Usize) : specs.generics.MyStruct.build.spec N k
  := by
  unfold specs.generics.MyStruct.build.spec specs.generics.MyStruct.build
  hax_mvcgen

theorem specs.generics.MyStruct.get.spec.proof {N : Std.Usize}
  (self : specs.generics.MyStruct N) :
  specs.generics.MyStruct.get.spec self
  := by
  unfold specs.generics.MyStruct.get.spec specs.generics.MyStruct.get
  hax_mvcgen

theorem Tuple.Insts.Hax_testsSpecsArgumentsSize.len.spec.proof (_ : Unit) :
  Tuple.Insts.Hax_testsSpecsArgumentsSize.len.spec ()
  := by
  unfold Tuple.Insts.Hax_testsSpecsArgumentsSize.len.spec Tuple.Insts.Hax_testsSpecsArgumentsSize.len
  hax_mvcgen

theorem
  specs.traits.B.provided.default.spec.proof {Self : Type} (BInst :
                                           specs.traits.B Self) (self : Self) :
  specs.traits.B.provided.default.spec BInst self
  := by
  unfold specs.traits.B.provided.default.spec specs.traits.B.provided.default
  intro h
  unfold specs.traits.B.provided.pre at h
  cases hv : BInst.AInst.a self
  · rw [hv] at h
    hax_mvcgen [specs.traits.B.provided.post, hv]
    simp
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem
  specs.traits.C.provided_c.default.spec.proof {Self : Type} (CInst :
                                             specs.traits.C Self) (self : Self)
  : specs.traits.C.provided_c.default.spec CInst self
  := by
  unfold specs.traits.C.provided_c.default.spec specs.traits.C.provided_c.default
  intro h
  unfold specs.traits.C.provided_c.pre at h
  cases hv : CInst.BInst.AInst.a self
  · rw [hv] at h
    hax_mvcgen [specs.traits.C.provided_c.post, hv]
    simp
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

/-- `is_even` and `is_odd` call each other: their triples are proved together,
by induction on `n`. -/
theorem specs.mutual.triples (k : Nat) (n : Std.U32) (h : n.val = k) :
    ⦃ ⌜ True ⌝ ⦄ specs.mutual.is_even n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 0) ⌝ ⦄ ∧
    ⦃ ⌜ True ⌝ ⦄ specs.mutual.is_odd n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 1) ⌝ ⦄ := by
  induction k generalizing n with
  | zero =>
    constructor
    · rw [specs.mutual.is_even]
      hax_mvcgen
      · agrind
      · exfalso; scalar_tac
      · exfalso; scalar_tac
    · rw [specs.mutual.is_odd]
      hax_mvcgen
      · agrind
      · exfalso; scalar_tac
      · exfalso; scalar_tac
  | succ k ih =>
    constructor
    · rw [specs.mutual.is_even]
      hax_mvcgen
      · exfalso; scalar_tac
      · next r _ _ =>
        have := (ih r (by scalar_tac)).2
        mvcgen [this]
        simp_all only [decide_eq_decide]
        scalar_tac
      · exfalso; scalar_tac
    · rw [specs.mutual.is_odd]
      hax_mvcgen
      · exfalso; scalar_tac
      · next r _ _ =>
        have := (ih r (by scalar_tac)).1
        mvcgen [this]
        simp_all only [decide_eq_decide]
        scalar_tac
      · exfalso; scalar_tac

@[spec]
theorem specs.mutual.is_even.triple (n : Std.U32) :
  ⦃ ⌜ True ⌝ ⦄ specs.mutual.is_even n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 0) ⌝ ⦄ :=
  (specs.mutual.triples _ n rfl).1

theorem specs.mutual.is_even.spec.proof (n : Std.U32) :
  specs.mutual.is_even.spec n
  := by
  unfold specs.mutual.is_even.spec
  hax_mvcgen [specs.mutual.is_even.pre, specs.mutual.is_even.post]
  agrind

@[spec]
theorem specs.mutual.is_odd.triple (n : Std.U32) :
  ⦃ ⌜ True ⌝ ⦄ specs.mutual.is_odd n ⦃ ⇓ res => ⌜ res = decide (n.val % 2 = 1) ⌝ ⦄ :=
  (specs.mutual.triples _ n rfl).2

theorem specs.mutual.is_odd.spec.proof (n : Std.U32) :
  specs.mutual.is_odd.spec n
  := by
  unfold specs.mutual.is_odd.spec
  hax_mvcgen [specs.mutual.is_odd.pre, specs.mutual.is_odd.post]
  agrind

end hax_tests
