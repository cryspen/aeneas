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

    Phase 1A: `bitwise` re-enabled. The RuntimeShim now registers
    `#isize` (alongside `#i32` and `#i64`), so the emitter's
    `16#isize` shift-amount literal in `shift_i32` typechecks
    without the hand-patch the committed
    `aeneas-lean-checker/tests/Generated/Bitwise.lean` used to need. -/
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[`incr_cert, `compare_simple, `calls, `bitwise]

/-- Common formatting + the per-fixture runners. -/
lean_lib «LeanDiff» where
  roots := #[`LeanDiff.Common,
             `LeanDiff.IncrRunner,
             `LeanDiff.CompareSimpleRunner,
             `LeanDiff.CallsRunner,
             `LeanDiff.BitwiseRunner]

/-- The differential entry point. Calls each runner's `runAll` so a
    single invocation produces the full expected-line stream. -/
@[default_target]
lean_exe «leandiff» where
  root := `LeanDiff.Main
  supportInterpreter := true
