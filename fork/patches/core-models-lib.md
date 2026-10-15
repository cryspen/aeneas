# core-models-lib

## Summary

Adds the Lean-only flag `-core-models-lib` (fork PRs #2, #6, #65, #75). Under it,
items of `core`, `alloc` and `std` are taken from the external
[rust-core-models](https://github.com/cryspen/rust-core-models) Lean library
(`CoreModels`) instead of the models in the Aeneas standard library:

- generated files import `CoreModels` and open `CoreModels Aeneas`, then
  `Aeneas.Std` hiding the `core`/`alloc` namespaces;
- the Lean overrides of `ExtractBuiltin` are disabled
  (`unless_core_models_lib`), except the ones that only fix a shape: the
  `Box::new` entry (it must stay the identity, `T -> T`, or the
  "not a result type" sanity check fires) and the allocator `keep_params` map;
- non-local items are skipped (`skip_for_core_models_lib`) and non-local trait
  impl names get a crate prefix;
- the `filter_eq_assert_fields_method` prepass removes `assert_fields_are_eq`
  from derived `Eq` impls;
- `compute_allocator_filter` drops the type parameters and trait clauses that
  Charon's `hide_allocator` pass leaves dangling, for non-local `core`/`alloc`/
  `std` items only: local items are declared by us, so their uses must keep all
  generics (#75).

## Invariants

- Without the flag, the output is byte-identical to upstream's.
- With the flag, no item from a non-local crate is emitted, and the flag is
  rejected for non-Lean backends.
- All Lean overrides from `ExtractBuiltinLean.ml` are disabled except the
  shape-only ones (`Box::new`, the allocator `keep_params` map). The
  backend-independent globals of `builtin_globals` (the integer `MIN`, `MAX`
  and `BITS` constants, `UNIT_METADATA`) stay active.
- The allocator filter never applies to local items.
- With the default `-use-lean-modules`, `CoreModels` must be a Lean module:
  generated files are modules and `public import CoreModels`.

## Tests

- `tests/src/core-models-lib.rs` (expected output
  `tests/lean/CoreModelsLib/CoreModelsLib.lean`, in a subdirectory so that
  `tests/lean` does not build it): derived `Eq`, `Box::new`, `Vec` methods,
  `callee`/`caller` and a loop with a `C: Op` generic (#75), a local impl of a
  non-local trait, `as_slice`, `[x; N]`, `Some` as a function.

## Rebase notes

- `tests/src/core-models-lib.rs` was written for this rebase. On the old base,
  `Some` used as a function was a name clash under the flag; since upstream
  #1330 it extracts to `core.option.Option.Some.constructor`.
- Since upstream #1320 (charon bump of 2026-09), array-to-slice and
  `core::array::repeat` are ordinary calls modelled in `ExtractBuiltinLean`
  (which this flag disables), and since #1330 constructor functions are
  separate (non-local) items. Under the flag they are emitted as
  `core.array.*` calls and `….constructor` references that `CoreModels` must
  provide; the test pins this. *(To be fixed in rust-core-models when hax pins
  this aeneas.)*
- `external-names` builds on this patch (`external_types_keep_params_map`).

## History

- 2026-10-07: bootstrapped from fork PRs #2, #6, #65, #75; ported to upstream's
  removal of LLBC builtin functions (#1320) and to Lean module-system output
  (#1230); the clause-filter length fix moved to `fix-trait-clause-filter-length`.
