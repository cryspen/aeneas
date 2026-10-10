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
- The conditions of a trait method take one trait clause per (transitive)
  supertrait, while the method reaches them through its `Self` clause: each
  clause of a condition is instantiated with the matching trait ref of the
  method or one of its parent clauses (`cond_generics`, #80).
- Conditions on a required trait method (no default body) are dropped,
  without a warning: no `pre`/`post`/spec/obligation is extracted for them
  (`traits.rs`, trait `D`).
- The names `<fn>.pre`, `<fn>.post`, `<fn>.spec` and `<fn>.spec.proof` derive
  from the registered name of `<fn>` (the conditions of a default method
  `<Trait>.<m>.default` are `<Trait>.<m>.pre`/`.post`). They are registered
  (`ExtractSpec.register_names`, ids `SpecId`/`ProofObligationId`) after the
  crate items, so a clash with an item of the crate is an error (#82).
- Obligations are plain theorems, not `@[spec]` lemmas: users register the
  specs they prove.
- Spec and obligation files are emitted only when non-empty; their imports come
  from `Spec.required_imports`.
- With the default `-use-lean-modules`, the hax proof library (`Hax`) must be a
  Lean module: generated files are modules and `public import Hax`.

## Tests

- `tests/hax` (fork PR #83) is a crate on `hax-lib` 0.4.2, extracted the way
  hax users do it: `cargo hax extract` runs the proof scenario `hax-tests` of
  `tests/hax/hax.toml`, which points hax at `bin/aeneas` and
  `charon/bin/charon`. The extracted code (`tests/hax/proofs/hax-tests/lean`,
  Lean package `HaxTests`, under `Extraction/`) is committed, next to
  handwritten assumptions (`Assumptions/`) and proofs of the obligations
  (`Verification/`). Every contract is proved; one that cannot be is left out
  of the crate, with a comment. `make verify-hax` checks that every obligation
  has a proof, not commented out and without `sorry`.
- The modules of `tests/hax/src/specs/`: the shape of contracts, arguments
  (unit arguments, #79), `&mut` inputs and `future`, generics, mutually
  recursive functions, trait methods (supertraits, direct and transitive, #80;
  the generic supertrait `H` has no contract, so the substitution of a parent
  clause's generics in `cond_generics` is untested, and the conditions of the
  required method `D::required` are dropped; see `traits.rs`) and names that
  look like generated ones without clashing (#82).
- Not run by `make test`: `make test-hax HAX_DIR=<hax checkout>`
  (`scripts/test-hax.sh`; `extract-hax` and `verify-hax` run the two steps)
  needs `cargo hax` and a checkout of hax. `make clean-generated-aeneas`
  leaves `tests/hax` alone.
- `make verify-hax` builds the extracted code against the Lean libraries
  (`Hax`, `CoreModels`) of the hax checkout, which must build against this
  aeneas: Lean modules, on aeneas's Lean toolchain (hax `main` does since
  721d1a27, 2026-11-04).

## Rebase notes

- `tests/hax` replaced `tests/src/hax_specs` (and the vendored `hax-lib` of
  the nix check, `haxSpecsVendor`). Tests that upstream-port commits add to
  `tests/src/hax_specs` belong in a module of `tests/hax/src/specs/` (e.g.
  `mutual.rs`, from the 2026-10-20 rebase), and the outputs must be
  re-extracted with `make extract-hax`.
- A bump of `backends/lean/lean-toolchain` must also update
  `tests/hax/proofs/hax-tests/lean/lean-toolchain` (`make verify-hax` checks
  it).
- The proof check of `scripts/test-hax.sh` (`verify`: every obligation of
  `Extraction/ProofObligations.lean` has a theorem of the same name under
  `Verification/`, without `sorry`) compares names only. Once hax runs Lean's
  comparator (which checks that the handwritten theorems state the extracted
  obligations and use no extra axioms), use it instead and drop this check.

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
- 2026-10-23: supertrait clauses are passed to the conditions of trait methods
  (fork PR #80).
- 2026-10-23: the names generated for specs are registered, and clashes are
  errors (fork PR #82).
- 2026-10-23: the tests moved to `tests/hax`, extracted end-to-end with
  `cargo hax` (fork PR #83).
- 2026-11-04: rebased on the 2026-11-02 dev (no change).
