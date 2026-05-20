import Lake
open Lake DSL

/-!
The Aeneas Lean checker.

After Phase 2a (Lean-emit retirement) this lib only depends on Lean
core (for `Lean.Json`). It validates the OCaml-side cert format and
the LLBC# trace replay, runs the cert-walker, and emits a pure-Rust
model. The Lean-emit backend (and its `RuntimeShim` runtime stub)
were dropped in this commit; the M10-verified replayer and the
Rust-model emit are what remains.
-/

package «aeneas-lean-checker» where

@[default_target] lean_lib «AeneasCheck» where

lean_exe «aeneas-check» where
  root := `AeneasCheck.Cli
  supportInterpreter := true
