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

/-- Minimal `Aeneas.Std` shim: just enough surface for the M7
    emitter's output to typecheck without pulling in the
    mathlib-backed real runtime in `backends/lean/`. See
    `RuntimeShim/Aeneas/Std.lean` for the design rationale. -/
lean_lib «RuntimeShim» where
  srcDir := "RuntimeShim"
  roots := #[`Aeneas, `Aeneas.Std]

/-- Compiles the M7-generated Lean source against `RuntimeShim`. The
    file at `tests/Generated/Incr.lean` is produced by running
    `aeneas-check --out tests/Generated/Incr.lean` (see
    `scripts/check-vertical-slice.sh`).

    M9.5c: `Generated.Reborrows` covers the cert-translated
    `set_fst` / `set_idx` / `reborrow_chain` from `tests/src/reborrows.rs`.
    The RuntimeShim grew `Aeneas.Std.Array` + `Array.update` + the
    `#usize` const-generic macro to make the shape compile. -/
lean_lib «GeneratedTests» where
  srcDir := "tests"
  roots := #[`Generated.Incr, `Generated.CompareSimple, `Generated.Calls,
             `Generated.LoopsSimple, `Generated.Reborrows,
             `Generated.EnumsBasic]
