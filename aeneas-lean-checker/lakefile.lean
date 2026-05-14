import Lake
open Lake DSL

/-!
The Aeneas Lean checker.

M4-M6: this lib only depends on Lean core (for `Lean.Json`). It validates
the OCaml-side cert format and the LLBC# trace replay; it does not yet
emit Lean source.

M7+ will add a dependency on `../backends/lean/` so the emitted Lean
output can reference `Aeneas.Std.U32`, `Result`, etc. unchanged. The
dependency is held off until then to keep the M4/M5/M6 build cycle
mathlib-free (faster CI, faster local iteration).
-/

package «aeneas-lean-checker» where

@[default_target] lean_lib «AeneasCheck» where

lean_exe «aeneas-check» where
  root := `AeneasCheck.Cli
  supportInterpreter := true
