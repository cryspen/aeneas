import Lake
open Lake DSL

-- Important: mathlib imports std4 and quote4: we mustn't add a `require std4` line
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0-rc2"

package «aeneas» where
  preferReleaseBuild := true
  buildArchive := s!"lean-build-aeneas-{System.Platform.target}.tar.gz"
  -- Lean v4.33 newly enables/strengthens these linters. They fire on generated
  -- Rust-path declaration names (`dupNamespace`, e.g. `core.clone…​.clone`),
  -- intentional `Prop`-valued definitions (`defProp`), and `open Std` now that
  -- `Lean.Std` also exists (`ambiguousOpen`). None are cleanly fixable in the
  -- generated / spec code, so we disable them to keep `lake build --iofail`
  -- (used in CI) green after the toolchain bump.
  leanOptions := #[
    ⟨`weak.linter.dupNamespace, false⟩,
    ⟨`weak.linter.defProp, false⟩,
    ⟨`weak.linter.ambiguousOpen, false⟩
  ]

@[default_target] lean_lib «Aeneas» {}

private def notCI : Bool := run_io
  return (← IO.getEnv "CI").isNone

@[default_target] lean_lib «AeneasMeta» {
  -- Precompiling modules triggers issues in CI so we deactivate this.
  precompileModules := notCI
}

/-- Generate the `.ml` file listing the definitions supported by the standard library. -/
lean_exe extract where
  root := `AeneasExtract
  supportInterpreter := true
