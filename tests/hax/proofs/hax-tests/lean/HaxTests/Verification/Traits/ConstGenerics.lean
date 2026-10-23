-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::const_generics`.
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

theorem U32.Insts.Hax_testsSpecsTraitsConst_genericsCg4.Lawful :
  specs.traits.const_generics.Cg.Lawful Std.U32 4#usize
  U32.Insts.Hax_testsSpecsTraitsConst_genericsCg4
  where
  f_spec := by
    intro self x hpre
    mvcgen [U32.Insts.Hax_testsSpecsTraitsConst_genericsCg4.f]
    simp [specs.traits.const_generics.Cg.f.pre, specs.traits.const_generics.Cg.f.post] at hpre ⊢
    scalar_tac

theorem U32.Insts.Hax_testsSpecsTraitsConst_genericsCg8.Lawful :
  specs.traits.const_generics.Cg.Lawful Std.U32 8#usize
  U32.Insts.Hax_testsSpecsTraitsConst_genericsCg8
  where
  f_spec := by
    intro self x hpre
    simp [specs.traits.const_generics.Cg.f.pre] at hpre
    mvcgen [U32.Insts.Hax_testsSpecsTraitsConst_genericsCg8.f]
    · simp [specs.traits.const_generics.Cg.f.post]
      scalar_tac
    · -- no overflow: `x < 8`
      scalar_tac

theorem ArrayU32N.Insts.Hax_testsSpecsTraitsConst_genericsCg.Lawful (N :
  Std.Usize) :
  specs.traits.const_generics.Cg.Lawful (Array Std.U32 N) N
  (ArrayU32N.Insts.Hax_testsSpecsTraitsConst_genericsCg N)
  where
  f_spec := by
    intro self x _
    mvcgen [ArrayU32N.Insts.Hax_testsSpecsTraitsConst_genericsCg.f]
    simp [specs.traits.const_generics.Cg.f.post]

theorem
  specs.traits.const_generics.use_cg.spec.proof {T : Type} (CgT4Inst :
                                               specs.traits.const_generics.Cg T
                                               4#usize) (t : T) (x : Std.Usize)
  (CgT4InstLawful : specs.traits.const_generics.Cg.Lawful T 4#usize CgT4Inst) :
  specs.traits.const_generics.use_cg.spec CgT4Inst t x CgT4InstLawful
  := by
  unfold specs.traits.const_generics.use_cg.spec specs.traits.const_generics.use_cg
  /- The conditions of `use_cg` are those of `f` at `N := 4` -/
  exact CgT4InstLawful.f_spec t x

end hax_tests
