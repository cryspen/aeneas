-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::default_methods`.
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

theorem U32.Insts.Hax_testsSpecsTraitsDefault_methodsD.Lawful :
  specs.traits.default_methods.D.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsDefault_methodsD
  where
  next_spec := by
    intro self hpre
    simp [U32.Insts.Hax_testsSpecsTraitsDefault_methodsD.base] at hpre
    mvcgen [U32.Insts.Hax_testsSpecsTraitsDefault_methodsD.next]
    · simp [U32.Insts.Hax_testsSpecsTraitsDefault_methodsD.base]
      agrind
    · agrind

theorem U64.Insts.Hax_testsSpecsTraitsDefault_methodsD.Lawful :
  specs.traits.default_methods.D.Lawful Std.U64
  U64.Insts.Hax_testsSpecsTraitsDefault_methodsD
  where
  next_spec := by
    intro self _
    mvcgen [specs.traits.default_methods.D.next.default]

end hax_tests
