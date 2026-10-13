-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- [hax_tests]: proof obligations
import Aeneas
import CoreModels
import HaxTests.Extraction.Types
import HaxTests.Extraction.Funs
import HaxTests.Extraction.Specs
import HaxTests.Verification.Lemmas
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

register_closure_specs hax_tests

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

theorem specs.contracts.returns_option.spec.proof (x : Std.U32) :
  specs.contracts.returns_option.spec x
  := by
  unfold specs.contracts.returns_option.spec specs.contracts.returns_option
  hax_mvcgen
  simp

theorem specs.contracts.returns_result.spec.proof (x : Std.U32) :
  specs.contracts.returns_result.spec x := by
  unfold specs.contracts.returns_result.spec specs.contracts.returns_result
  hax_mvcgen [specs.contracts.returns_result.pre, specs.contracts.returns_result.post]
  · agrind
  · agrind
  · agrind

theorem specs.contracts.may_panic.spec.proof (x : Std.U32) (y : Std.U32) :
  specs.contracts.may_panic.spec x y
  := by
  unfold specs.contracts.may_panic.spec specs.contracts.may_panic
  hax_mvcgen [specs.contracts.may_panic.pre, specs.contracts.may_panic.post]
  · simp_all [Nat.div_le_self]
  · scalar_tac

theorem specs.contracts.explicit_panic.spec.proof (x : Std.U32) :
  specs.contracts.explicit_panic.spec x
  := by
  unfold specs.contracts.explicit_panic.spec specs.contracts.explicit_panic
  hax_mvcgen [specs.contracts.explicit_panic.pre, specs.contracts.explicit_panic.post]
  · simp_all
  · scalar_tac

theorem specs.generics.generic.spec.proof (N : Std.U32) (x : Std.U32) :
  specs.generics.generic.spec N x
  := by
  unfold specs.generics.generic.spec specs.generics.generic
  hax_mvcgen [specs.generics.generic.pre, specs.generics.generic.post]
  · simp; scalar_tac
  · scalar_tac

theorem specs.generics.trait_clause.spec.proof {T : Type} (ValInst :
                                             specs.generics.Val T)
  (t : T) (x : Std.U32) : specs.generics.trait_clause.spec ValInst t x := by
  unfold specs.generics.trait_clause.spec specs.generics.trait_clause specs.generics.trait_clause.pre
  simp only [bind_assoc_eq, bind_tc_ok, RustM.holds_bind_iff, forall_exists_index, and_imp]
  intros
  simp_all
  hax_mvcgen [specs.generics.trait_clause.post]
  · agrind
  · agrind

theorem specs.generics.where_clause.spec.proof {T : Type} (ValInst :
                                             specs.generics.Val T)
  (t : T) : specs.generics.where_clause.spec ValInst t := by
  unfold specs.generics.where_clause.spec specs.generics.where_clause specs.generics.where_clause.pre
  simp only [bind_assoc_eq, bind_tc_ok, RustM.holds_bind_iff, forall_exists_index, and_imp]
  intros
  simp_all
  hax_mvcgen [specs.generics.where_clause.post]

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

theorem specs.mutable_borrows.read_shared.spec.proof (x : Std.U32) :
  specs.mutable_borrows.read_shared.spec x
  := by
  unfold specs.mutable_borrows.read_shared.spec specs.mutable_borrows.read_shared
  hax_mvcgen
  simp

theorem specs.mutable_borrows.add_assign.spec.proof (x : Std.U32) (y : Std.U32) :
  specs.mutable_borrows.add_assign.spec x y
  := by
  unfold specs.mutable_borrows.add_assign.spec specs.mutable_borrows.add_assign
  hax_mvcgen [specs.mutable_borrows.add_assign.pre, specs.mutable_borrows.add_assign.post]
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

theorem specs.contracts.implies_cond.spec.proof (x : Std.U32)
  (y : Std.U32) : specs.contracts.implies_cond.spec x y
  := by
  unfold specs.contracts.implies_cond.spec specs.contracts.implies_cond
  hax_mvcgen [specs.contracts.implies_cond.pre, specs.contracts.implies_cond.post]
  · agrind
  · agrind
  · simp

theorem specs.contracts.quantifiers.spec.proof (x : Std.U32) :
  specs.contracts.quantifiers.spec x
  := by
  unfold specs.contracts.quantifiers.spec specs.contracts.quantifiers
  hax_mvcgen [specs.contracts.quantifiers.pre, specs.contracts.quantifiers.post]
  refine ⟨x, ?_⟩
  hax_mvcgen
  simp

theorem specs.contracts.int_bounds.spec.proof (x : Std.U32) (y : Std.U32)
  : specs.contracts.int_bounds.spec x y
  := by
  unfold specs.contracts.int_bounds.spec specs.contracts.int_bounds
  simp only [specs.contracts.int_bounds.pre, specs.contracts.int_bounds.post,
    core.cmp.PartialOrd.le.default.Int_eq]
  hax_mvcgen
  · agrind
  · simp_all [U32.rMax]; scalar_tac

theorem specs.contracts.helper_in_requires.spec.proof (x : Std.U32) :
  specs.contracts.helper_in_requires.spec x := by
  unfold specs.contracts.helper_in_requires.spec specs.contracts.helper_in_requires
  hax_mvcgen [specs.contracts.helper_in_requires.pre, specs.contracts.helper_in_requires.post, specs.contracts.is_small]
  · agrind
  · agrind
  · agrind

theorem specs.contracts.calls_contracted.spec.proof (x : Std.U32) :
  specs.contracts.calls_contracted.spec x := by
  unfold specs.contracts.calls_contracted.spec specs.contracts.calls_contracted
  hax_mvcgen [specs.contracts.calls_contracted.pre, specs.contracts.calls_contracted.post, specs.contracts.both]
  · agrind
  · agrind
  · agrind
  · agrind
  · agrind

/-- Opaque wrapper of the specification of `recursive`, so that the induction
hypothesis is not processed by `hax_mvcgen` while it is stuck on the recursive call. -/
def specs.contracts.recursive.Spec (n : Std.U32) : Prop :=
  ⦃ ⌜ True ⌝ ⦄ specs.contracts.recursive n ⦃ ⇓ res => ⌜ res = n ⌝ ⦄

theorem specs.contracts.recursive.Spec.of_val (k : Nat) (n : Std.U32) (h : n.val = k) :
    specs.contracts.recursive.Spec n := by
  induction k generalizing n with
  | zero =>
    unfold specs.contracts.recursive.Spec
    rw [specs.contracts.recursive]
    hax_mvcgen
    · agrind
    · agrind
    · exfalso; scalar_tac
  | succ k ih =>
    unfold specs.contracts.recursive.Spec
    rw [specs.contracts.recursive]
    hax_mvcgen
    · agrind
    · next r _ _ =>
      have := ih r (by scalar_tac)
      unfold specs.contracts.recursive.Spec at this
      mvcgen [this]
      · agrind
      · exfalso; scalar_tac
    · exfalso; scalar_tac

@[spec]
theorem specs.contracts.recursive.triple (n : Std.U32) :
  ⦃ ⌜ True ⌝ ⦄ specs.contracts.recursive n ⦃ ⇓ res => ⌜ res = n ⌝ ⦄ :=
  specs.contracts.recursive.Spec.of_val _ n rfl

theorem specs.contracts.recursive.spec.proof (n : Std.U32) :
  specs.contracts.recursive.spec n
  := by
  unfold specs.contracts.recursive.spec
  hax_mvcgen [specs.contracts.recursive.pre, specs.contracts.recursive.post]
  · agrind

@[spec]
theorem specs.contracts.with_loop_loop.triple (iter : core.ops.range.Range Std.U32)
    (acc : Std.U32) (h_le : iter.start.val ≤ iter.end.val)
    (h_bound : acc.val + (iter.end.val - iter.start.val) ≤ Std.U32.max) :
    ⦃ ⌜ True ⌝ ⦄ specs.contracts.with_loop_loop iter acc
    ⦃ ⇓ res => ⌜ res.val = acc.val + (iter.end.val - iter.start.val) ⌝ ⦄ := by
  unfold specs.contracts.with_loop_loop
  apply loop_spec
    (fun (x : core.ops.range.Range Std.U32 × Std.U32) =>
      x.1.start.val ≤ x.1.end.val ∧ x.1.end = iter.end ∧
      x.2.val + (x.1.end.val - x.1.start.val) = acc.val + (iter.end.val - iter.start.val))
    (· < ·) (fun x => x.1.end.val - x.1.start.val) wellFounded_lt
  · agrind
  · rintro ⟨⟨s, e⟩, a⟩ hx
    unfold specs.contracts.with_loop_loop.body
    hax_mvcgen
    · scalar_tac
    · exfalso; agrind
    · simp [PostCond.okAssertion]
      scalar_tac

theorem specs.contracts.with_loop.spec.proof (n : Std.U32) :
  specs.contracts.with_loop.spec n
  := by
  unfold specs.contracts.with_loop.spec specs.contracts.with_loop
  hax_mvcgen [specs.contracts.with_loop.pre, specs.contracts.with_loop.post]
  · agrind
  · scalar_tac
  · agrind

theorem specs.arguments.sum_fields.spec.proof (p : specs.arguments.Point) :
  specs.arguments.sum_fields.spec p
  := by
  unfold specs.arguments.sum_fields.spec specs.arguments.sum_fields
  hax_mvcgen [specs.arguments.sum_fields.pre, specs.arguments.sum_fields.post]
  · agrind
  · agrind
  · agrind

theorem specs.arguments.shape_len.spec.proof
  (s : specs.arguments.Shape) : specs.arguments.shape_len.spec s := by
  unfold specs.arguments.shape_len.spec specs.arguments.shape_len
  cases s
  · hax_mvcgen [specs.arguments.shape_len.pre, specs.arguments.shape_len.post]
  · hax_mvcgen [specs.arguments.shape_len.pre, specs.arguments.shape_len.post]
    · agrind
    · agrind

theorem specs.generics.assoc_type.spec.proof {P : Type} (ProducerPU32Inst :
                                           specs.generics.Producer P
                                           Std.U32) (p : P) :
  specs.generics.assoc_type.spec ProducerPU32Inst p := by
  unfold specs.generics.assoc_type.spec specs.generics.assoc_type specs.generics.assoc_type.pre
  simp only [bind_assoc_eq, bind_tc_ok, RustM.holds_bind_iff, forall_exists_index, and_imp]
  intros
  simp_all
  hax_mvcgen [specs.generics.assoc_type.post]

theorem specs.generics.array_index.spec.proof {N : Std.Usize} (x : Array Std.U32 N) (i : Std.Usize) :
  specs.generics.array_index.spec x i
  := by
  unfold specs.generics.array_index.spec specs.generics.array_index
  hax_mvcgen [specs.generics.array_index.pre, specs.generics.array_index.post]
  · agrind
  · agrind
  · agrind

theorem specs.generics.nothing_no_args.spec.proof (T : Type) :
  specs.generics.nothing_no_args.spec T
  := by
  unfold specs.generics.nothing_no_args.spec specs.generics.nothing_no_args
  hax_mvcgen [specs.generics.nothing_no_args.post]

theorem specs.mutable_borrows.Counter.bump.spec.proof (self : specs.mutable_borrows.Counter) :
  specs.mutable_borrows.Counter.bump.spec self
  := by
  unfold specs.mutable_borrows.Counter.bump.spec specs.mutable_borrows.Counter.bump
  hax_mvcgen [specs.mutable_borrows.Counter.bump.pre, specs.mutable_borrows.Counter.bump.post]
  · agrind
  · agrind
  · agrind

theorem specs.generics.Wrapper.inner_value.spec.proof {T : Type} (ValInst :
                                                    specs.generics.Val T)
  (self : specs.generics.Wrapper T) :
  specs.generics.Wrapper.inner_value.spec ValInst self := by
  unfold specs.generics.Wrapper.inner_value.spec specs.generics.Wrapper.inner_value specs.generics.Wrapper.inner_value.pre
  simp only [bind_assoc_eq, bind_tc_ok, RustM.holds_bind_iff, forall_exists_index, and_imp]
  intros
  simp_all
  hax_mvcgen [specs.generics.Wrapper.inner_value.post]

end hax_tests
