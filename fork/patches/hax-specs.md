# hax-specs

## Summary

With `-specs hax`, `hax_lib::requires`/`ensures` annotations become Lean specs
and proof obligations (fork PRs #7, #58, #62). For `f` with a precondition and a
postcondition, Aeneas emits `f.pre`, `f.post`, `f.spec` and an `@[spec]`
obligation `f.spec.proof`. The design is generic: `src/specs/Spec.ml` is the
spec interface, `src/specs/HaxProducer.ml` gathers hax specs (helpers in
`src/utils/HaxAttributes.ml`), `src/extract/ExtractSpec.ml` dispatches the
printing and `src/extract/ExtractHaxSpecs.ml` prints hax specs. Two backends:
`mvcgen`-style (`-specs hax`) and `step`-style (`-specs hax-step`).

A prepass (`HaxLateSkipFilterPrePass`) removes the items hax marks as
`late_skip` (helper items without a `Uid`); decoration functions (with a `Uid`)
are consumed by the producer.

## Invariants

- Without `-specs`, the output is unchanged and the prepass is a no-op.
- Decoration functions never appear as such; only as `<fn>.pre`/`<fn>.post`.
- Arguments of spec functions are printed with `Extract.extract_App` (#58).
- Spec and obligation files are emitted only when non-empty; their imports come
  from `Spec.required_imports`.
- With the default `-use-lean-modules`, the hax proof library (`Hax`) must be a
  Lean module: generated files are modules and `public import Hax`.

## Tests

- `tests/src/hax_specs` (expected outputs `tests/lean/HaxSpecs`) and
  `tests/src/hax_specs_step` (same sources, `tests/lean/HaxSpecsStep`): basic
  specs, const and trait generics, `future`, implicit generics, mutually
  recursive functions.
- The `hax-lib` crates are vendored for the nix check (`haxSpecsVendor` in
  `flake.nix`).

## History

- 2026-10-07: bootstrapped from fork PRs #7, #58, #62; ported to upstream's
  removal of LLBC builtin functions (#1320) and module-system output (#1230).
