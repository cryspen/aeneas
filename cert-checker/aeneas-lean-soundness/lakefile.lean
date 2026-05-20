import Lake
open Lake DSL

/-!
The Aeneas LLBC# soundness proof.

M10 (Phases A–F) replaces the four axioms in
`AeneasSoundness/Soundness/StepEventSound.lean`
(`LLBCState`, `concretise`, `Valid`, `LStep`) with a fully Lean-mechanized
LLBC# semantics + per-event soundness proofs. Composed with the paper's
Theorems 3.1 / 3.3 / 4.1 / 4.2 (trusted base until the optional Phase G
port), this yields `cert_implies_pl_safety`: every cert accepted by
`AeneasCheck.LLBCSharp.Replay.replayCrate` witnesses the safe execution
of its embedded LLBC program.

This package is mathlib-dependent. The checker (`aeneas-lean-checker`)
stays mathlib-free for its ~1 s build; soundness builds in its own
slower lane (~30 min cold; ~5 min warm — G7 budget).

The Mathlib version is pinned in `.mathlib-pin` (currently
`v4.30.0-rc2`, matching the toolchain). Bumps go through a dedicated
PR at phase boundaries, never mid-phase.
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

require «aeneas-lean-checker» from "../aeneas-lean-checker"

package «aeneas-lean-soundness» where

@[default_target] lean_lib «AeneasSoundness» where
