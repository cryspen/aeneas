-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::diamond`.
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

theorem U8.Insts.Hax_testsSpecsTraitsDiamondA.Lawful :
  specs.traits.diamond.A.Lawful Std.U8 U8.Insts.Hax_testsSpecsTraitsDiamondA
  where
  a_spec := by
    intro self _
    mvcgen [U8.Insts.Hax_testsSpecsTraitsDiamondA.a]

theorem U8.Insts.Hax_testsSpecsTraitsDiamondB.Lawful :
  specs.traits.diamond.B.Lawful Std.U8 U8.Insts.Hax_testsSpecsTraitsDiamondB
  := ⟨U8.Insts.Hax_testsSpecsTraitsDiamondA.Lawful⟩

theorem U8.Insts.Hax_testsSpecsTraitsDiamondC.Lawful :
  specs.traits.diamond.C.Lawful Std.U8 U8.Insts.Hax_testsSpecsTraitsDiamondC
  where
  AInstLawful := U8.Insts.Hax_testsSpecsTraitsDiamondA.Lawful
  BInstLawful := U8.Insts.Hax_testsSpecsTraitsDiamondB.Lawful
  c_spec := by
    intro self _
    mvcgen [U8.Insts.Hax_testsSpecsTraitsDiamondC.c, U8.Insts.Hax_testsSpecsTraitsDiamondA.a]

theorem
  specs.traits.diamond.via_b.spec.proof {T : Type} (BInst :
                                       specs.traits.diamond.B T) (x : T)
  (BInstLawful : specs.traits.diamond.B.Lawful T BInst) :
  specs.traits.diamond.via_b.spec BInst x BInstLawful
  := by
  unfold specs.traits.diamond.via_b.spec specs.traits.diamond.via_b
  have ha := BInstLawful.AInstLawful.a_spec
  mvcgen [ha]

theorem
  specs.traits.diamond.diamond.spec.proof {T : Type} (CInst :
                                         specs.traits.diamond.C T) (x : T)
  (CInstLawful : specs.traits.diamond.C.Lawful T CInst) :
  specs.traits.diamond.diamond.spec CInst x CInstLawful
  := by
  unfold specs.traits.diamond.diamond.spec specs.traits.diamond.diamond
  /- Modular: `x.a()` goes through `CInst.AInst` (paired with
  `CInstLawful.AInstLawful`), `via_b x` through `CInst.BInst` (paired with
  `CInstLawful.BInstLawful`, via `via_b`'s spec, without unfolding `via_b`). -/
  obtain ⟨a, ha, hapost⟩ := Aeneas.Std.WP.triple_iff_exists_ok.1 (CInstLawful.AInstLawful.a_spec x (by simp))
  have hvb := specs.traits.diamond.via_b.spec.proof CInst.BInst x CInstLawful.BInstLawful
  unfold specs.traits.diamond.via_b.spec at hvb
  obtain ⟨b, hb, hbpost⟩ := Aeneas.Std.WP.triple_iff_exists_ok.1 hvb
  simp [specs.traits.diamond.A.a.post] at hapost
  simp [specs.traits.diamond.via_b.post] at hbpost
  mvcgen [ha, hb]
  · simp [specs.traits.diamond.diamond.post]
    agrind
  · -- no overflow: both summands are ≤ 100
    agrind

end hax_tests
