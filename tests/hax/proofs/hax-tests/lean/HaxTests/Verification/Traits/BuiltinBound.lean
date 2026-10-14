-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::builtin_bound`.
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

theorem U32.Insts.Hax_testsSpecsTraitsBuiltin_boundDup.Lawful :
  specs.traits.builtin_bound.Dup.Lawful Std.U32
  U32.Insts.Hax_testsSpecsTraitsBuiltin_boundDup
  where
  corecloneCloneInstLawful := core.U32.Insts.CoreCloneClone.Lawful
  dup_spec := by
    intro self _
    mvcgen [U32.Insts.Hax_testsSpecsTraitsBuiltin_boundDup.dup]

theorem specs.traits.builtin_bound.One.Insts.CoreCloneClone.Lawful :
  core.clone.Clone.Lawful specs.traits.builtin_bound.One
  specs.traits.builtin_bound.One.Insts.CoreCloneClone
  where
  clone_spec x := by
    mvcgen [specs.traits.builtin_bound.One.Insts.CoreCloneClone.clone]

theorem specs.traits.builtin_bound.One.Insts.CoreDefaultDefault.Lawful :
  core.default.Default.Lawful specs.traits.builtin_bound.One
  specs.traits.builtin_bound.One.Insts.CoreDefaultDefault
  := ⟨⟩

theorem
  specs.traits.builtin_bound.One.Insts.Hax_testsSpecsTraitsBuiltin_boundDup.Lawful
  :
  specs.traits.builtin_bound.Dup.Lawful specs.traits.builtin_bound.One
  specs.traits.builtin_bound.One.Insts.Hax_testsSpecsTraitsBuiltin_boundDup
  where
  corecloneCloneInstLawful :=
    specs.traits.builtin_bound.One.Insts.CoreCloneClone.Lawful
  dup_spec := by
    intro self _
    mvcgen [specs.traits.builtin_bound.One.Insts.Hax_testsSpecsTraitsBuiltin_boundDup.dup,
      specs.traits.builtin_bound.One.Insts.CoreCloneClone.clone]

theorem specs.traits.builtin_bound.W.Insts.CoreCloneClone.Lawful {T : Type}
  (corecloneCloneInst : core.clone.Clone T)
  (corecloneCloneInstLawful : core.clone.Clone.Lawful T corecloneCloneInst) :
  core.clone.Clone.Lawful (specs.traits.builtin_bound.W T)
  (specs.traits.builtin_bound.W.Insts.CoreCloneClone corecloneCloneInst)
  where
  clone_spec w := by
    -- `W`'s derived `clone` clones the field: use the inner `clone_spec`
    have h := corecloneCloneInstLawful.clone_spec
    mvcgen [specs.traits.builtin_bound.W.Insts.CoreCloneClone.clone, h]

theorem
  specs.traits.builtin_bound.WU32.Insts.Hax_testsSpecsTraitsBuiltin_boundDup.Lawful
  :
  specs.traits.builtin_bound.Dup.Lawful (specs.traits.builtin_bound.W Std.U32)
  specs.traits.builtin_bound.WU32.Insts.Hax_testsSpecsTraitsBuiltin_boundDup
  where
  corecloneCloneInstLawful :=
    specs.traits.builtin_bound.W.Insts.CoreCloneClone.Lawful
      core.U32.Insts.CoreCloneClone core.U32.Insts.CoreCloneClone.Lawful
  dup_spec := by
    intro self _
    -- reuse the `Clone.Lawful` proof of `W U32` rather than unfolding both `clone` layers
    have h := (specs.traits.builtin_bound.W.Insts.CoreCloneClone.Lawful
      core.U32.Insts.CoreCloneClone core.U32.Insts.CoreCloneClone.Lawful).clone_spec
    mvcgen [specs.traits.builtin_bound.WU32.Insts.Hax_testsSpecsTraitsBuiltin_boundDup.dup, h]

theorem
  specs.traits.builtin_bound.dup.spec.proof {T : Type} (corecloneCloneInst :
                                           core.clone.Clone T) (x : T)
  (corecloneCloneInstLawful : core.clone.Clone.Lawful T corecloneCloneInst) :
  specs.traits.builtin_bound.dup.spec corecloneCloneInst x
  corecloneCloneInstLawful
  := by
  unfold specs.traits.builtin_bound.dup.spec specs.traits.builtin_bound.dup
  -- `clone` cannot fail by the `Clone.Lawful` hypothesis
  obtain ⟨a, ha, -⟩ := Aeneas.Std.WP.triple_iff_exists_ok.1 (corecloneCloneInstLawful.clone_spec x)
  rw [ha]
  hax_mvcgen [specs.traits.builtin_bound.dup.post]

end hax_tests
