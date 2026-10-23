-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::assoc_consts`.
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

theorem U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.Lawful :
  specs.traits.assoc_consts.Bounded.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded
  where
  clamp_spec := by
    intro self x hpre
    mvcgen [U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.clamp]
    /- `MAX` is a monadic field of the instance: the conditions bind it -/
    simp [specs.traits.assoc_consts.Bounded.clamp.pre, specs.traits.assoc_consts.Bounded.clamp.post] at hpre ⊢
    agrind

theorem U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.clamp.spec.proof
   (self : Std.U32) (x : Std.U32) :
  U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.clamp.spec self x
  := by
  unfold U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.clamp.spec U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.clamp
  hax_mvcgen

theorem U32.Insts.Hax_testsSpecsTraitsAssoc_constsScaled.Lawful :
  specs.traits.assoc_consts.Scaled.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsAssoc_constsScaled
  where
  BoundedInstLawful := U32.Insts.Hax_testsSpecsTraitsAssoc_constsBounded.Lawful
  scale_spec := by
    intro self x hpre
    mvcgen [U32.Insts.Hax_testsSpecsTraitsAssoc_constsScaled.scale]
    /- `MIN` takes its default value, through `ScaledInst.BoundedInst` -/
    simp [specs.traits.assoc_consts.Scaled.scale.pre, specs.traits.assoc_consts.Scaled.scale.post] at hpre ⊢
    /- The `else` branch of the precondition is contradictory -/
    split at hpre <;> simp at hpre
    agrind

theorem
  specs.traits.assoc_consts.use_clamp.spec.proof {T : Type} (BoundedInst :
                                                specs.traits.assoc_consts.Bounded
                                                T) (t : T) (x : Std.U32)
  (BoundedInstLawful : specs.traits.assoc_consts.Bounded.Lawful T BoundedInst)
  : specs.traits.assoc_consts.use_clamp.spec BoundedInst t x BoundedInstLawful
  := by
  unfold specs.traits.assoc_consts.use_clamp.spec specs.traits.assoc_consts.use_clamp
  /- The conditions of `use_clamp` are those of `clamp`, `T::MAX` being `Self::MAX` -/
  exact BoundedInstLawful.clamp_spec t x

end hax_tests
