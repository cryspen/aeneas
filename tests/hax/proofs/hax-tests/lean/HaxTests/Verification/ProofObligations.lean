-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- [hax_tests]: proof obligations
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

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

namespace hax_tests

theorem standalone.contracts.only_requires.spec.proof (x : Std.U32) :
  standalone.contracts.only_requires.spec x
  := by
  unfold standalone.contracts.only_requires.spec standalone.contracts.only_requires
  hax_mvcgen
  scalar_tac

theorem standalone.contracts.only_ensures.spec.proof (x : Std.U32) : standalone.contracts.only_ensures.spec x
  := by
  unfold standalone.contracts.only_ensures.spec standalone.contracts.only_ensures
  hax_mvcgen
  simp

theorem standalone.contracts.both.spec.proof (x : Std.U32) : standalone.contracts.both.spec x := by
  unfold standalone.contracts.both.spec standalone.contracts.both
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac

theorem standalone.contracts.no_args.spec.proof : standalone.contracts.no_args.spec := by
  unfold standalone.contracts.no_args.spec standalone.contracts.no_args
  hax_mvcgen

theorem standalone.contracts.returns_unit.spec.proof (x : Std.U32) : standalone.contracts.returns_unit.spec x
  := by
  unfold standalone.contracts.returns_unit.spec standalone.contracts.returns_unit
  hax_mvcgen

theorem standalone.contracts.block_in_requires.spec.proof (x : Std.U32) :
  standalone.contracts.block_in_requires.spec x
  := by
  unfold standalone.contracts.block_in_requires.spec standalone.contracts.block_in_requires
  hax_mvcgen

theorem standalone.contracts.returns_pair.spec.proof (x : Std.U32) : standalone.contracts.returns_pair.spec x
  := by
  unfold standalone.contracts.returns_pair.spec standalone.contracts.returns_pair
  hax_mvcgen
  simp

theorem standalone.contracts.returns_option.spec.proof (x : Std.U32) :
  standalone.contracts.returns_option.spec x
  := by
  unfold standalone.contracts.returns_option.spec standalone.contracts.returns_option
  hax_mvcgen
  simp

theorem standalone.contracts.returns_result.spec.proof (x : Std.U32) :
  standalone.contracts.returns_result.spec x
  := by
  unfold standalone.contracts.returns_result.spec standalone.contracts.returns_result
  hax_mvcgen [standalone.contracts.returns_result.pre, standalone.contracts.returns_result.post]
  all_goals simp_all
  all_goals scalar_tac

theorem standalone.contracts.may_panic.spec.proof (x : Std.U32) (y : Std.U32) :
  standalone.contracts.may_panic.spec x y
  := by
  unfold standalone.contracts.may_panic.spec standalone.contracts.may_panic
  hax_mvcgen [standalone.contracts.may_panic.pre, standalone.contracts.may_panic.post]
  · simp_all [Nat.div_le_self]
  · scalar_tac

theorem standalone.contracts.explicit_panic.spec.proof (x : Std.U32) :
  standalone.contracts.explicit_panic.spec x
  := by
  unfold standalone.contracts.explicit_panic.spec standalone.contracts.explicit_panic
  hax_mvcgen [standalone.contracts.explicit_panic.pre, standalone.contracts.explicit_panic.post]
  · simp_all
  · scalar_tac

theorem standalone.generics.generic.spec.proof (N : Std.U32) (x : Std.U32) :
  standalone.generics.generic.spec N x
  := by
  unfold standalone.generics.generic.spec standalone.generics.generic
  hax_mvcgen [standalone.generics.generic.pre, standalone.generics.generic.post]
  · simp; scalar_tac
  · scalar_tac

theorem standalone.generics.trait_clause.spec.proof {T : Type} (ValInst : standalone.generics.Val T)
  (t : T) (x : Std.U32) : standalone.generics.trait_clause.spec ValInst t x
  := by
  unfold standalone.generics.trait_clause.spec standalone.generics.trait_clause
  intro h
  unfold standalone.generics.trait_clause.pre at h
  cases hv : ValInst.value t
  · rw [hv] at h
    hax_mvcgen [standalone.generics.trait_clause.post]
    · simp; scalar_tac
    · scalar_tac
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem standalone.generics.where_clause.spec.proof {T : Type} (ValInst : standalone.generics.Val T)
  (t : T) : standalone.generics.where_clause.spec ValInst t
  := by
  unfold standalone.generics.where_clause.spec standalone.generics.where_clause
  intro h
  unfold standalone.generics.where_clause.pre at h
  cases hv : ValInst.value t
  · rw [hv] at h
    hax_mvcgen [standalone.generics.where_clause.post]
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem standalone.mutable_borrows.incr.spec.proof (x : Std.U32) : standalone.mutable_borrows.incr.spec x := by
  unfold standalone.mutable_borrows.incr.spec standalone.mutable_borrows.incr
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem standalone.mutable_borrows.incr_i.spec.proof (x : Slice Std.U32) (i : Std.Usize) :
  standalone.mutable_borrows.incr_i.spec x i
  := by
  unfold standalone.mutable_borrows.incr_i.spec standalone.mutable_borrows.incr_i
  hax_mvcgen [standalone.mutable_borrows.incr_i.pre, standalone.mutable_borrows.incr_i.post, core.slice.Slice.len]
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

theorem standalone.mutable_borrows.swap_and_add.spec.proof (x : Std.U32) (y : Std.U32) :
  standalone.mutable_borrows.swap_and_add.spec x y
  := by
  unfold standalone.mutable_borrows.swap_and_add.spec standalone.mutable_borrows.swap_and_add
  hax_mvcgen [standalone.mutable_borrows.swap_and_add.pre, standalone.mutable_borrows.swap_and_add.post]
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem standalone.mutable_borrows.read_shared.spec.proof (x : Std.U32) :
  standalone.mutable_borrows.read_shared.spec x
  := by
  unfold standalone.mutable_borrows.read_shared.spec standalone.mutable_borrows.read_shared
  hax_mvcgen
  simp

theorem standalone.mutable_borrows.add_assign.spec.proof (x : Std.U32) (y : Std.U32) :
  standalone.mutable_borrows.add_assign.spec x y
  := by
  unfold standalone.mutable_borrows.add_assign.spec standalone.mutable_borrows.add_assign
  hax_mvcgen [standalone.mutable_borrows.add_assign.pre, standalone.mutable_borrows.add_assign.post]
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem standalone.generics.nothing.spec.proof (T : Type) (k : Std.Usize) :
  standalone.generics.nothing.spec T k
  := by
  unfold standalone.generics.nothing.spec standalone.generics.nothing
  hax_mvcgen

theorem standalone.generics.of_fst.spec.proof {T : Type} (N : Std.Usize) 
  (t : T) : standalone.generics.of_fst.spec N t
  := by
  unfold standalone.generics.of_fst.spec standalone.generics.of_fst
  hax_mvcgen

theorem standalone.generics.empty.spec.proof (T : Type) (N : Std.Usize)
  (k : Std.Usize) : standalone.generics.empty.spec T N k
  := by
  unfold standalone.generics.empty.spec standalone.generics.empty
  hax_mvcgen

theorem standalone.arguments.named.spec.proof (_ : Unit) : standalone.arguments.named.spec ()
  := by
  unfold standalone.arguments.named.spec standalone.arguments.named
  hax_mvcgen

theorem standalone.arguments.before_other.spec.proof (_ : Unit) (y : Std.U32) :
  standalone.arguments.before_other.spec () y
  := by
  unfold standalone.arguments.before_other.spec standalone.arguments.before_other
  hax_mvcgen
  simp

theorem standalone.naming.foo.spec.proof (x : Std.U32) : standalone.naming.foo.spec x
  := by
  unfold standalone.naming.foo.spec standalone.naming.foo
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
  · scalar_tac

theorem standalone.generics.MyStruct.build.spec.proof (N : Std.Usize)
  (k : Std.Usize) : standalone.generics.MyStruct.build.spec N k
  := by
  unfold standalone.generics.MyStruct.build.spec standalone.generics.MyStruct.build
  hax_mvcgen

theorem standalone.generics.MyStruct.get.spec.proof {N : Std.Usize}
  (self : standalone.generics.MyStruct N) :
  standalone.generics.MyStruct.get.spec self
  := by
  unfold standalone.generics.MyStruct.get.spec standalone.generics.MyStruct.get
  hax_mvcgen

theorem Tuple.Insts.Hax_testsStandaloneArgumentsSize.len.spec.proof (_ : Unit) :
  Tuple.Insts.Hax_testsStandaloneArgumentsSize.len.spec ()
  := by
  unfold Tuple.Insts.Hax_testsStandaloneArgumentsSize.len.spec Tuple.Insts.Hax_testsStandaloneArgumentsSize.len
  hax_mvcgen

theorem
  standalone.traits.B.provided.default.spec.proof {Self : Type} (BInst :
                                           standalone.traits.B Self) (self : Self) :
  standalone.traits.B.provided.default.spec BInst self
  := by
  unfold standalone.traits.B.provided.default.spec standalone.traits.B.provided.default
  intro h
  unfold standalone.traits.B.provided.pre at h
  cases hv : BInst.AInst.a self
  · rw [hv] at h
    hax_mvcgen [standalone.traits.B.provided.post, hv]
    simp
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

theorem
  standalone.traits.C.provided_c.default.spec.proof {Self : Type} (CInst :
                                             standalone.traits.C Self) (self : Self)
  : standalone.traits.C.provided_c.default.spec CInst self
  := by
  unfold standalone.traits.C.provided_c.default.spec standalone.traits.C.provided_c.default
  intro h
  unfold standalone.traits.C.provided_c.pre at h
  cases hv : CInst.BInst.AInst.a self
  · rw [hv] at h
    hax_mvcgen [standalone.traits.C.provided_c.post, hv]
    simp
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h
  · rw [hv] at h
    simp [Triple, WP.wp, PredTrans.apply, Functor.map] at h

end hax_tests
