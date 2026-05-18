import Lake
open Lake DSL

/-!
Lean-side differential testing harness.

This Lake project is intentionally **mathlib-free**: it reuses the
`RuntimeShim` library from `aeneas-lean-checker/RuntimeShim/`, which
mirrors enough of `Aeneas.Std` for emitter-generated source to
typecheck. The full `backends/lean/` (which depends on mathlib)
would take >10min cold to build; the shim is seconds.

Per-fixture flow:
  1. `aeneas-check <cert>.json --out generated/<Fixture>.lean`
  2. `generated/<Fixture>.lean` imports `Aeneas` -> resolves to
     `RuntimeShim/Aeneas.lean`.
  3. `LeanDiff/<Fixture>Runner.lean` imports the generated module
     and prints one stable line per test vector via `IO.println`.
  4. The `leandiff` exe runs every fixture's table; the Rust runner
     produces byte-identical lines from native Rust; a `diff`
     confirms equivalence.
-/

package «lean-diff» where

/-- The minimal `Aeneas.Std` shim used by the emitter pipeline. We
    *do not* duplicate it — we point Lake at the existing files in
    `aeneas-lean-checker/RuntimeShim/`. -/
lean_lib «RuntimeShim» where
  srcDir := "../../../aeneas-lean-checker/RuntimeShim"
  roots := #[`Aeneas, `Aeneas.Std]

/-- The emitter-generated fixture source. Files in `generated/` are
    produced by `aeneas-check --out`; we just compile them.

    NOTE: `bitwise` is intentionally excluded — the M10-era emitter
    on this branch produces `16#isize` for the `>>>` rhs in
    `shift_i32`, but the RuntimeShim only registers a `#usize` /
    `#u32` macro. The committed `aeneas-lean-checker/tests/Generated/
    Bitwise.lean` predates that emitter regression and uses
    `(16 : Std.Isize)` instead, hiding the gap from gate G3. Tracked
    in the LeanEmit observations in the final report. -/
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[`incr_cert, `compare_simple, `calls]

/-- Common formatting + the per-fixture runners. -/
lean_lib «LeanDiff» where
  roots := #[`LeanDiff.Common,
             `LeanDiff.IncrRunner,
             `LeanDiff.CompareSimpleRunner,
             `LeanDiff.CallsRunner]

/-- The differential entry point. Calls each runner's `runAll` so a
    single invocation produces the full expected-line stream. -/
@[default_target]
lean_exe «leandiff» where
  root := `LeanDiff.Main
  supportInterpreter := true
