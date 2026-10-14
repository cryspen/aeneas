-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::unannotated_sub`.
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

theorem U32.Insts.Hax_testsSpecsTraitsUnannotated_subA.Lawful :
  specs.traits.unannotated_sub.A.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsUnannotated_subA
  where
  a_spec := by
    intro self _
    mvcgen [U32.Insts.Hax_testsSpecsTraitsUnannotated_subA.a]

theorem U32.Insts.Hax_testsSpecsTraitsUnannotated_subB.Lawful :
  specs.traits.unannotated_sub.B.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsUnannotated_subB
  := ⟨U32.Insts.Hax_testsSpecsTraitsUnannotated_subA.Lawful⟩

end hax_tests
