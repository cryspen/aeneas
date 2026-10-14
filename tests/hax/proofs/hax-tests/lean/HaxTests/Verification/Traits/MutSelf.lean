-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::mut_self`.
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

theorem U32.Insts.Hax_testsSpecsTraitsMut_selfCounter.Lawful :
  specs.traits.mut_self.Counter.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsMut_selfCounter
  where
  incr_spec := by
    intro self hpre
    simp [U32.Insts.Hax_testsSpecsTraitsMut_selfCounter.get] at hpre
    -- `self + 1` does not overflow under the precondition.
    obtain ⟨r, hr, -⟩ :=
      WP.spec_imp_exists (U32.add_bv_spec (x := self) (y := 1#u32) (by scalar_tac))
    mvcgen [U32.Insts.Hax_testsSpecsTraitsMut_selfCounter.incr, hr]
    simp [U32.Insts.Hax_testsSpecsTraitsMut_selfCounter.get, hr]

end hax_tests
