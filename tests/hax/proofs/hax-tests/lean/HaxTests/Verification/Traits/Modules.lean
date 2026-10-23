-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::modules`.
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

theorem specs.traits.modules.c.S.Insts.Hax_testsSpecsTraitsModulesABT.Lawful :
  specs.traits.modules.a.b.T.Lawful specs.traits.modules.c.S
  specs.traits.modules.c.S.Insts.Hax_testsSpecsTraitsModulesABT
  where
  t_spec := by
    intro self _
    mvcgen [specs.traits.modules.c.S.Insts.Hax_testsSpecsTraitsModulesABT.t]

theorem specs.traits.modules.W.Insts.Hax_testsSpecsTraitsModulesABT.Lawful {U :
  Type} (abTInst : specs.traits.modules.a.b.T U)
  (abTInstLawful : specs.traits.modules.a.b.T.Lawful U abTInst) :
  specs.traits.modules.a.b.T.Lawful (specs.traits.modules.W U)
  (specs.traits.modules.W.Insts.Hax_testsSpecsTraitsModulesABT abTInst)
  where
  t_spec self hpre := abTInstLawful.t_spec self hpre

theorem
  specs.traits.modules.impl_arg.spec.proof {T0 : Type} (abTInst :
                                          specs.traits.modules.a.b.T T0)
  (x : T0) (abTInstLawful : specs.traits.modules.a.b.T.Lawful T0 abTInst) :
  specs.traits.modules.impl_arg.spec abTInst x abTInstLawful
  := by
  unfold specs.traits.modules.impl_arg.spec specs.traits.modules.impl_arg
  have h := abTInstLawful.t_spec
  mvcgen [h]

end hax_tests
