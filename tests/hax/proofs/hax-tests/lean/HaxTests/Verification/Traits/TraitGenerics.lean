-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::trait_generics`.
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

theorem U32.Insts.Hax_testsSpecsTraitsTrait_genericsConvU8.Lawful :
  specs.traits.trait_generics.Conv.Lawful Std.U32 Std.U8
  U32.Insts.Hax_testsSpecsTraitsTrait_genericsConvU8
  where
  conv_spec := by
    intro self t _
    mvcgen [U32.Insts.Hax_testsSpecsTraitsTrait_genericsConvU8.conv]

theorem
  specs.traits.trait_generics.use_conv.spec.proof {C : Type} (ConvCU8Inst :
                                                 specs.traits.trait_generics.Conv
                                                 C Std.U8) (c : C)
  (ConvCU8InstLawful : specs.traits.trait_generics.Conv.Lawful C Std.U8
  ConvCU8Inst) :
  specs.traits.trait_generics.use_conv.spec ConvCU8Inst c ConvCU8InstLawful
  := by
  unfold specs.traits.trait_generics.use_conv.spec
    specs.traits.trait_generics.use_conv
  -- The Lawful binder gives `conv`'s contract at `T := Std.U8`.
  have hc := ConvCU8InstLawful.conv_spec
  mvcgen [hc]

end hax_tests
