# hax-trait-specs

## Summary

Extends `hax-specs` to the contracts of traits (fork PR #85). Every local trait
`X` gets a companion structure `X.Lawful` (in `Specs.lean`) with one field
`<P>InstLawful` per parent clause and one field `<m>_spec` per method with a
`#[requires]`/`#[ensures]` contract, stated over `X.<m>.pre`/`X.<m>.post`.
Every local trait impl, including derived impls and impls of foreign traits,
gets an obligation `<impl>.Lawful` (in `ProofObligations.lean`). The specs of
functions with trait clauses take a Lawful hypothesis per clause. When a trait
method has only one of `#[requires]`/`#[ensures]`, the other condition is
synthesized, with body `ok true`. Contracts on the methods of an impl are
checked as standalone specs, independent of the trait contract (with a
warning when the trait method has a contract too).

The `hax-specs` IR (`src/specs/HaxSpecs.ml`) has trait specs and impl
obligations; `src/specs/HaxProducer.ml` gathers the contracts of trait methods
and the impls; `src/extract/ExtractHaxSpecs.ml` prints the Lawful structures,
hypotheses and obligations. Unsupported contracts are dropped with a
`hax-specs:` warning rather than failing the extraction. `-specs hax` now
requires `-core-models-lib`.

The user documentation is `documentation/hax-specs.md` (overview, file
structure, diagnostics, limitations, proof recipes).

## Invariants

- Without `-specs`, the output is unchanged.
- `-specs hax` without `-core-models-lib` is a command-line error.
- `X.Lawful` is only generated for local traits: for a foreign trait, the
  generated code refers to `X.Lawful` as if it existed, and a Lean library
  (`CoreModels`) must provide it.
- `Specs.lean` lists the traits parents first; `ProofObligations.lean` lists
  the impl obligations dependencies first, then the function obligations.
- The generated `.Lawful` names are registered with the other spec names: a
  clash with a crate item (e.g. an associated type `Lawful`) is an error.
- A contract that cannot be extracted is dropped with a warning (an error
  under `-warnings-as-errors`); the extraction continues. Each entry of
  `Specs.lean`/`ProofObligations.lean` is printed only if it extracts: a
  dropped entry leaves no partial output.

## Tests

- `tests/hax/src/specs/traits/` (expected outputs in
  `tests/hax/proofs/hax-tests/lean/HaxTests/Extraction`): basic contracts,
  supertraits and diamonds, generic and blanket impls, default methods,
  method, trait and const generics, associated constants and type bounds,
  `&mut self`, modules, built-in bounds, unannotated subtraits, impl-level
  contracts and synthesized conditions (the unsupported cases are commented
  out in `synthesized.rs`).
- `tests/hax/proofs/hax-tests/lean/HaxTests/Verification/Traits/`: proofs of
  the trait-level obligations; `Verification/Lemmas.lean` holds the
  `RustM.holds_bool` simp lemma they use.
- `tests/src/hax-specs-no-core-models-lib.rs`: the `-specs hax` flag check.

## Rebase notes

- Depends on `hax-specs` and `core-models-lib`.
- The `tests/hax` outputs are produced by `cargo hax extract`: re-extract them
  with `make extract-hax HAX_DIR=<hax checkout>` and re-check the proofs with
  `make verify-hax` (see `hax-specs`).

## History

- 2026-10-23: bootstrapped from fork PR #85, rebased on the 2026-10-20 fork;
  `tests/hax/src/specs.rs` keeps `hax-specs`'s `mutual` module.
