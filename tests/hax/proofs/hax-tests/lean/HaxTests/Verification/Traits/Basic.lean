-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::basic`.
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

theorem U64.Insts.Hax_testsSpecsTraitsBasicFoo.Lawful :
  specs.traits.basic.Foo.Lawful Std.U64 U64.Insts.Hax_testsSpecsTraitsBasicFoo
  where
  f1_spec := by
    intro self _
    mvcgen [U64.Insts.Hax_testsSpecsTraitsBasicFoo.f1]
  f2_spec := by
    intro self hpre
    mvcgen [U64.Insts.Hax_testsSpecsTraitsBasicFoo.f2]
  make_spec := by
    intro x _
    apply Aeneas.Std.WP.spec_to_mvcgen
    simp [U64.Insts.Hax_testsSpecsTraitsBasicFoo.make]
    step*
    simp [specs.traits.basic.Foo.make.post, U64.Insts.Hax_testsSpecsTraitsBasicFoo.f1]
    scalar_tac
  zero_spec := by
    intro _
    mvcgen [U64.Insts.Hax_testsSpecsTraitsBasicFoo.zero, U64.Insts.Hax_testsSpecsTraitsBasicFoo.f1]

theorem U32.Insts.Hax_testsSpecsTraitsBasicFoo.Lawful :
  specs.traits.basic.Foo.Lawful Std.U32 U32.Insts.Hax_testsSpecsTraitsBasicFoo
  where
  f1_spec := by
    intro self _
    mvcgen [U32.Insts.Hax_testsSpecsTraitsBasicFoo.f1]
  f2_spec := by
    intro self hpre
    mvcgen [U32.Insts.Hax_testsSpecsTraitsBasicFoo.f2]
  make_spec := by
    intro x _
    apply Aeneas.Std.WP.spec_to_mvcgen
    simp [U32.Insts.Hax_testsSpecsTraitsBasicFoo.make]
    step*
    simp [specs.traits.basic.Foo.make.post, U32.Insts.Hax_testsSpecsTraitsBasicFoo.f1]
    scalar_tac
  zero_spec := by
    intro _
    mvcgen [U32.Insts.Hax_testsSpecsTraitsBasicFoo.zero, U32.Insts.Hax_testsSpecsTraitsBasicFoo.f1]

theorem
  specs.traits.basic.g.spec.proof {T : Type} (FooInst : specs.traits.basic.Foo
                                 T) (x : T)
  (FooInstLawful : specs.traits.basic.Foo.Lawful T FooInst) :
  specs.traits.basic.g.spec FooInst x FooInstLawful
  := by
  unfold specs.traits.basic.g.spec specs.traits.basic.g
  /- `mvcgen [FooInstLawful.f2_spec]` cannot resolve a local projection: go through `have`. -/
  have h2 := FooInstLawful.f2_spec
  /- `f2`'s pre re-runs `f1 x`: pin its value with the equality recovered from `f1_spec`. -/
  obtain ⟨b, hf1, -⟩ := (Aeneas.Std.WP.triple_iff_exists_ok).1 (FooInstLawful.f1_spec x (by simp))
  mvcgen [hf1, h2]
  -- `else` branch: `0 <= 10`
  simp [specs.traits.basic.g.post]

theorem specs.traits.basic.h.spec.proof (x : Std.U64) :
  specs.traits.basic.h.spec x
  := by
  unfold specs.traits.basic.h.spec specs.traits.basic.h
  have hg := specs.traits.basic.g.spec.proof U64.Insts.Hax_testsSpecsTraitsBasicFoo x
    U64.Insts.Hax_testsSpecsTraitsBasicFoo.Lawful
  unfold specs.traits.basic.g.spec at hg
  mvcgen [hg]

end hax_tests
