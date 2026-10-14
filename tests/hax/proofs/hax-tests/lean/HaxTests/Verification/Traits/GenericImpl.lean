-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::generic_impl`.
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

namespace hax_tests

theorem U64.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful :
  specs.traits.generic_impl.Foo.Lawful Std.U64
  U64.Insts.Hax_testsSpecsTraitsGeneric_implFoo
  where
  f_spec := by
    intro self _
    mvcgen [U64.Insts.Hax_testsSpecsTraitsGeneric_implFoo.f]

theorem
  specs.traits.generic_impl.Wrapper.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful
  {T : Type} (FooInst : specs.traits.generic_impl.Foo T)
  (FooInstLawful : specs.traits.generic_impl.Foo.Lawful T FooInst) :
  specs.traits.generic_impl.Foo.Lawful (specs.traits.generic_impl.Wrapper T)
  (specs.traits.generic_impl.Wrapper.Insts.Hax_testsSpecsTraitsGeneric_implFoo
  FooInst)
  where
  f_spec self hpre := FooInstLawful.f_spec self.inner hpre

theorem
  specs.traits.generic_impl.Wrapper.Insts.Hax_testsSpecsTraitsGeneric_implSub.Lawful
  {T : Type} (SubInst : specs.traits.generic_impl.Sub T)
  (SubInstLawful : specs.traits.generic_impl.Sub.Lawful T SubInst) :
  specs.traits.generic_impl.Sub.Lawful (specs.traits.generic_impl.Wrapper T)
  (specs.traits.generic_impl.Wrapper.Insts.Hax_testsSpecsTraitsGeneric_implSub
  SubInst)
  where
  FooInstLawful :=
    specs.traits.generic_impl.Wrapper.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful
      SubInst.FooInst SubInstLawful.FooInstLawful
  s_spec self hpre := SubInstLawful.s_spec self.inner hpre

theorem Pair.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful {T : Type} {U :
  Type} (FooInst : specs.traits.generic_impl.Foo T) (FooInst1 :
  specs.traits.generic_impl.Foo U)
  (FooInstLawful : specs.traits.generic_impl.Foo.Lawful T FooInst)
  (FooInst1Lawful : specs.traits.generic_impl.Foo.Lawful U FooInst1) :
  specs.traits.generic_impl.Foo.Lawful (T × U)
  (Pair.Insts.Hax_testsSpecsTraitsGeneric_implFoo FooInst FooInst1)
  where
  f_spec := by
    intro self hpre
    obtain ⟨t, u⟩ := self
    exact FooInstLawful.f_spec t hpre

theorem
  specs.traits.generic_impl.Single.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful
  {T : Type} (FooInst : specs.traits.generic_impl.Foo T)
  (FooInstLawful : specs.traits.generic_impl.Foo.Lawful T FooInst) :
  specs.traits.generic_impl.Foo.Lawful (specs.traits.generic_impl.Single T)
  (specs.traits.generic_impl.Single.Insts.Hax_testsSpecsTraitsGeneric_implFoo
  FooInst)
  where
  f_spec self hpre := FooInstLawful.f_spec self hpre

theorem
  specs.traits.generic_impl.SingleU64.Insts.Hax_testsSpecsTraitsGeneric_implSub.Lawful
  :
  specs.traits.generic_impl.Sub.Lawful (specs.traits.generic_impl.Single
  Std.U64)
  specs.traits.generic_impl.SingleU64.Insts.Hax_testsSpecsTraitsGeneric_implSub
  where
  FooInstLawful :=
    specs.traits.generic_impl.Single.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful
      U64.Insts.Hax_testsSpecsTraitsGeneric_implFoo
      U64.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful
  s_spec := by
    intro self _
    mvcgen [specs.traits.generic_impl.SingleU64.Insts.Hax_testsSpecsTraitsGeneric_implSub.s,
      specs.traits.generic_impl.Single.Insts.Hax_testsSpecsTraitsGeneric_implFoo.f,
      U64.Insts.Hax_testsSpecsTraitsGeneric_implFoo.f]

theorem
  specs.traits.generic_impl.k.spec.proof {T : Type} {U : Type} (FooInst :
                                        specs.traits.generic_impl.Foo T)
                                        (SubInst :
                                        specs.traits.generic_impl.Sub U)
  (x : T) (y : U)
  (FooInstLawful : specs.traits.generic_impl.Foo.Lawful T FooInst)
  (SubInstLawful : specs.traits.generic_impl.Sub.Lawful U SubInst) :
  specs.traits.generic_impl.k.spec FooInst SubInst x y FooInstLawful
  SubInstLawful
  := by
  unfold specs.traits.generic_impl.k.spec specs.traits.generic_impl.k
  have h1 := FooInstLawful.f_spec
  have h2 := SubInstLawful.s_spec
  /- `s`'s post is `res = SubInst.FooInst.f y`: evaluate the parent's `f` on
     `y` once, through the parent Lawful field. -/
  obtain ⟨i, hfy, hi⟩ := Aeneas.Std.WP.triple_iff_exists_ok.1
    (SubInstLawful.FooInstLawful.f_spec y (by simp))
  mvcgen [h1, h2]
  · -- `f x <= 10` and `s y = f y <= 10`
    simp [hfy] at *
    agrind
  · -- no overflow: the sum is at most 20
    simp [hfy] at *
    agrind

end hax_tests
