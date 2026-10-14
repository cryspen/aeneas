-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::assoc_type_bounds`.
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

theorem U32.Insts.Hax_testsSpecsTraitsAssoc_type_boundsBar.Lawful :
  specs.traits.assoc_type_bounds.Bar.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsAssoc_type_boundsBar
  where
  bar_spec := by
    intro self _
    mvcgen [U32.Insts.Hax_testsSpecsTraitsAssoc_type_boundsBar.bar]

theorem
  specs.traits.assoc_type_bounds.One.Insts.Hax_testsSpecsTraitsAssoc_type_boundsContainerU32.Lawful
  :
  specs.traits.assoc_type_bounds.Container.Lawful
  specs.traits.assoc_type_bounds.One Std.U32
  specs.traits.assoc_type_bounds.One.Insts.Hax_testsSpecsTraitsAssoc_type_boundsContainerU32
  where
  BarInstLawful := U32.Insts.Hax_testsSpecsTraitsAssoc_type_boundsBar.Lawful
  first_spec := by
    intro self _
    -- the post calls `bar` on the result, through the impl's `BarInst`
    mvcgen [specs.traits.assoc_type_bounds.One.Insts.Hax_testsSpecsTraitsAssoc_type_boundsContainerU32.first,
      U32.Insts.Hax_testsSpecsTraitsAssoc_type_boundsBar.bar]

theorem
  specs.traits.assoc_type_bounds.Box1.Insts.Hax_testsSpecsTraitsAssoc_type_boundsContainer.Lawful
  {T : Type} (BarInst1 : specs.traits.assoc_type_bounds.Bar T)
  (coremarkerCopyInst : core.marker.Copy T)
  (BarInst1Lawful : specs.traits.assoc_type_bounds.Bar.Lawful T BarInst1)
  (coremarkerCopyInstLawful : core.marker.Copy.Lawful T coremarkerCopyInst) :
  specs.traits.assoc_type_bounds.Container.Lawful
  (specs.traits.assoc_type_bounds.Box1 T) T
  (specs.traits.assoc_type_bounds.Box1.Insts.Hax_testsSpecsTraitsAssoc_type_boundsContainer
  BarInst1 coremarkerCopyInst)
  where
  BarInstLawful := BarInst1Lawful
  first_spec := by
    intro self hpre
    /- `first` is the identity on `Box1 T = T`, and the post calls
       `BarInst1.bar` on it: evaluate it once through `BarInst1Lawful`. -/
    obtain ⟨i, hb, hi⟩ :=
      Aeneas.Std.WP.triple_iff_exists_ok.1 (BarInst1Lawful.bar_spec self hpre)
    mvcgen [specs.traits.assoc_type_bounds.Box1.Insts.Hax_testsSpecsTraitsAssoc_type_boundsContainer.first]
    simpa [hb] using hi

theorem
  specs.traits.assoc_type_bounds.first_bar.spec.proof {C : Type} {Clause0_Item
                                                     : Type} (ContainerInst :
                                                     specs.traits.assoc_type_bounds.Container
                                                     C Clause0_Item) 
  (c : C)
  (ContainerInstLawful : specs.traits.assoc_type_bounds.Container.Lawful C
  Clause0_Item ContainerInst) :
  specs.traits.assoc_type_bounds.first_bar.spec ContainerInst c
  ContainerInstLawful
  := by
  unfold specs.traits.assoc_type_bounds.first_bar.spec specs.traits.assoc_type_bounds.first_bar
  have h1 := ContainerInstLawful.first_spec
  have h2 := ContainerInstLawful.BarInstLawful.bar_spec
  -- `Bar.bar.post` and `first_bar.post` are both `ok (res < 10#u32)`: defeq
  mvcgen [h1, h2]

end hax_tests
