# hax-specs

## Summary

With `-specs hax`, `hax_lib::requires`/`ensures` annotations become Lean specs
and proof obligations (fork PRs #7, #58, #62). For `f` with a precondition and a
postcondition, Aeneas emits `f.pre`, `f.post`, `f.spec` and an obligation
`f.spec.proof`. The design is generic: `src/specs/Spec.ml` is the spec
interface, `src/specs/HaxProducer.ml` gathers hax specs (helpers in
`src/utils/HaxAttributes.ml`), `src/extract/ExtractSpec.ml` dispatches the
printing and `src/extract/ExtractHaxSpecs.ml` prints hax specs. `f.spec` is an
`mvcgen`-style Hoare triple (files that use specs `open Std.Do`); the
`step`-style backend (`-specs hax-step`) was removed (fork PR #76).

A prepass (`HaxLateSkipFilterPrePass`) removes the items hax marks as
`late_skip` (helper items without a `Uid`); decoration functions (with a `Uid`)
are consumed by the producer.

## Invariants

- Without `-specs`, the output is unchanged and the prepass is a no-op.
- Decoration functions never appear as such; only as `<fn>.pre`/`<fn>.post`.
- Arguments of spec functions are printed with `Extract.extract_App` (#58).
- Specs and obligations pass every input of the function, in order: unit
  inputs, which are extracted as `_` binders, are passed as `()` (#79).
- Obligations are plain theorems, not `@[spec]` lemmas: users register the
  specs they prove.
- Spec and obligation files are emitted only when non-empty; their imports come
  from `Spec.required_imports`.
- With the default `-use-lean-modules`, the hax proof library (`Hax`) must be a
  Lean module: generated files are modules and `public import Hax`.

## Tests

- `tests/src/hax_specs` (expected outputs `tests/lean/HaxSpecs`): basic specs,
  const and trait generics, `future`, implicit generics, mutually recursive
  functions, unit arguments (#79).
- The `hax-lib` crates are vendored for the nix check (`haxSpecsVendor` in
  `flake.nix`).

## History

- 2026-10-07: bootstrapped from fork PRs #7, #58, #62; ported to upstream's
  removal of LLBC builtin functions (#1320) and module-system output (#1230).
- 2026-10-20: ported to the removal of `replace_static` (#1438) and the
  promoted-constant pre-passes (#1404); the late-skip filter keeps its place
  after `filter_type_aliases`.
- 2026-10-23: the `step`-style backend (`-specs hax-step`, its test
  `tests/src/hax_specs_step` and the `@[spec]` attribute on obligations) removed
  (fork PR #76).
- 2026-10-23: unit arguments are kept in specs and obligations (fork PR #79).
