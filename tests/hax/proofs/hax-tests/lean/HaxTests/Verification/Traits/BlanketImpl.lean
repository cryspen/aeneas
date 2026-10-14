-- Handwritten proofs of the obligations of `Extraction/ProofObligations.lean`.
-- Covers the test module `hax_tests::specs::traits::blanket_impl`.
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

theorem specs.traits.blanket_impl.Show.Blanket.Lawful (T : Type) :
  specs.traits.blanket_impl.Show.Lawful T
  (specs.traits.blanket_impl.Show.Blanket T)
  where
  show_spec := by
    intro self _
    mvcgen [specs.traits.blanket_impl.Show.Blanket.show]

theorem specs.traits.blanket_impl.Tag.Blanket.Lawful {T : Type} (ShowInst1 :
  specs.traits.blanket_impl.Show T)
  (ShowInst1Lawful : specs.traits.blanket_impl.Show.Lawful T ShowInst1) :
  specs.traits.blanket_impl.Tag.Lawful T (specs.traits.blanket_impl.Tag.Blanket
  ShowInst1)
  := ⟨ShowInst1Lawful⟩

theorem specs.traits.blanket_impl.show_generic.spec.proof {T : Type} 
  (x : T) : specs.traits.blanket_impl.show_generic.spec x
  := by
  unfold specs.traits.blanket_impl.show_generic.spec
    specs.traits.blanket_impl.show_generic
  -- `Show` comes from `Show.Blanket T`: use its Lawful term.
  have hs := (specs.traits.blanket_impl.Show.Blanket.Lawful T).show_spec
  mvcgen [hs]

theorem specs.traits.blanket_impl.show_u64.spec.proof (x : Std.U64) :
  specs.traits.blanket_impl.show_u64.spec x
  := by
  unfold specs.traits.blanket_impl.show_u64.spec specs.traits.blanket_impl.show_u64
  -- `Show` comes from `Show.Blanket Std.U64`: use the blanket theorem at `Std.U64`.
  have hs := (specs.traits.blanket_impl.Show.Blanket.Lawful Std.U64).show_spec
  mvcgen [hs]

end hax_tests
