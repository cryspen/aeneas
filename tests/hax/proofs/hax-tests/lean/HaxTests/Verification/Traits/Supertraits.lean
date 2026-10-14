-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::supertraits`.
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

theorem U8.Insts.Hax_testsSpecsTraitsSupertraitsA.Lawful :
  specs.traits.supertraits.A.Lawful Std.U8
  U8.Insts.Hax_testsSpecsTraitsSupertraitsA
  where
  a_spec := by
    intro self _
    mvcgen [U8.Insts.Hax_testsSpecsTraitsSupertraitsA.a]

theorem U8.Insts.Hax_testsSpecsTraitsSupertraitsB.Lawful :
  specs.traits.supertraits.B.Lawful Std.U8
  U8.Insts.Hax_testsSpecsTraitsSupertraitsB
  where
  AInstLawful := U8.Insts.Hax_testsSpecsTraitsSupertraitsA.Lawful
  b_spec := by
    intro self _
    apply Aeneas.Std.WP.spec_to_mvcgen
    simp [U8.Insts.Hax_testsSpecsTraitsSupertraitsB.b, U8.Insts.Hax_testsSpecsTraitsSupertraitsA.a]
    step*

theorem U8.Insts.Hax_testsSpecsTraitsSupertraitsCc.Lawful :
  specs.traits.supertraits.Cc.Lawful Std.U8
  U8.Insts.Hax_testsSpecsTraitsSupertraitsCc
  where
  BInstLawful := U8.Insts.Hax_testsSpecsTraitsSupertraitsB.Lawful
  c_spec := by
    /- `c = b = a + 1 = 2`; the post reaches `a` through
    `CcInst.BInst.AInst = U8.Insts.Hax_testsSpecsTraitsSupertraitsA`. -/
    intro self _
    apply Aeneas.Std.WP.spec_to_mvcgen
    simp [U8.Insts.Hax_testsSpecsTraitsSupertraitsCc.c, U8.Insts.Hax_testsSpecsTraitsSupertraitsB.b, U8.Insts.Hax_testsSpecsTraitsSupertraitsA.a]
    step*

theorem
  specs.traits.supertraits.via_b.spec.proof {T : Type} (BInst :
                                           specs.traits.supertraits.B T)
  (x : T) (BInstLawful : specs.traits.supertraits.B.Lawful T BInst) :
  specs.traits.supertraits.via_b.spec BInst x BInstLawful
  := by
  unfold specs.traits.supertraits.via_b.spec specs.traits.supertraits.via_b
  intro hpre
  /- `x.a()` (and the pre) through `BInstLawful.AInstLawful.a_spec`, `x.b()` through
  `BInstLawful.b_spec`, whose pre (`a x < 100`) is `via_b`'s pre and whose post
  (`b x > a x`) rules out the underflow. -/
  obtain ⟨a, ha, -⟩ := Aeneas.Std.WP.triple_iff_exists_ok.1 (BInstLawful.AInstLawful.a_spec x (by simp))
  simp [ha, specs.traits.supertraits.via_b.pre] at hpre
  obtain ⟨b, hb, hgt⟩ := Aeneas.Std.WP.triple_iff_exists_ok.1 (BInstLawful.b_spec x (by simpa [ha] using hpre))
  simp [ha] at hgt
  mvcgen [ha, hb]
  · simp [specs.traits.supertraits.via_b.post]
    agrind
  · -- no underflow: `b x > a x`
    agrind

theorem specs.traits.supertraits.via_u8.spec.proof (x : Std.U8) :
  specs.traits.supertraits.via_u8.spec x
  := by
  /- `via_u8` is `via_b` at the `u8` impls. -/
  exact specs.traits.supertraits.via_b.spec.proof _ x U8.Insts.Hax_testsSpecsTraitsSupertraitsB.Lawful

end hax_tests
