-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::impl_contract`.
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

theorem U32.Insts.Hax_testsSpecsTraitsImpl_contractFoo.Lawful :
  specs.traits.impl_contract.Foo.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsImpl_contractFoo
  := ⟨⟩

theorem U32.Insts.Hax_testsSpecsTraitsImpl_contractG.Lawful :
  specs.traits.impl_contract.G.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsImpl_contractG
  where
  g_spec := by
    intro self _
    /- `self % 10 + 1` cannot overflow and is positive, whatever `self`: the
       trait-level contract holds without the impl-level `requires`. -/
    mvcgen [U32.Insts.Hax_testsSpecsTraitsImpl_contractG.g]
    · agrind
    · agrind

theorem U32.Insts.Hax_testsSpecsTraitsImpl_contractFoo.f.spec.proof
  (self : Std.U32) : U32.Insts.Hax_testsSpecsTraitsImpl_contractFoo.f.spec self
  := by
  unfold U32.Insts.Hax_testsSpecsTraitsImpl_contractFoo.f.spec U32.Insts.Hax_testsSpecsTraitsImpl_contractFoo.f
  hax_mvcgen
  · agrind
  · agrind
  · agrind

theorem U32.Insts.Hax_testsSpecsTraitsImpl_contractG.g.spec.proof
  (self : Std.U32) : U32.Insts.Hax_testsSpecsTraitsImpl_contractG.g.spec self
  := by
  unfold U32.Insts.Hax_testsSpecsTraitsImpl_contractG.g.spec U32.Insts.Hax_testsSpecsTraitsImpl_contractG.g
  hax_mvcgen
  · agrind
  · agrind
  · agrind

end hax_tests
