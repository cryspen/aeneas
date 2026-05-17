import AeneasSoundness.LLBCSharpPaper.Syntax
import AeneasSoundness.LLBCSharpPaper.State
import AeneasSoundness.LLBCSharpPaper.Program
import AeneasSoundness.LLBCSharpPaper.WellFormed
import AeneasSoundness.LLBCSharpPaper.Step
import AeneasSoundness.LLBCSharpPaper.Valid
import AeneasSoundness.Soundness.Concretise.Defn
import AeneasSoundness.Soundness.Concretise.Lemmas
import AeneasSoundness.Soundness.StepEventSound

/-!
Top-level module for the Aeneas LLBC# soundness package.

The soundness proof closes the four axioms in
`AeneasSoundness/Soundness/StepEventSound.lean`
(`LLBCState`, `concretise`, `Valid`, `LStep`) into a fully
Lean-mechanized theorem that *`replayCrate` accepting a cert implies the
existence of a valid LLBC# derivation*, and by composition with the
paper's Theorems 3.1 / 3.3 / 4.1 / 4.2 (trusted base), PL-level safety.

Trust boundary (post-M10): this package plus the Lean kernel plus
`CertGen_faithful` (the OCaml interpreter's honesty assumption) plus the
four paper-theorem axioms (until Phase G) are the TCB for the
end-to-end safety claim.
-/

namespace AeneasSoundness

/-- Library version. Bump when changing public API. -/
def version : String := "0.1.0-dev"

end AeneasSoundness
