# core-models-lib

## Summary

Adds the Lean-only flag `-core-models-lib` (fork PRs #2, #6, #65, #75, #77).
Under it, items of `core`, `alloc` and `std` are taken from the external
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
  generics (#75). Only allocators are dropped (#77): an impl parameter is
  droppable only if it does not appear in the impl header (Rust forbids that,
  E0207, so it is an allocator whose argument was hidden), and an item's own
  parameter only if `Extract.core_models_fun_allocator_params` lists it
  (e.g. the `A` of `<[T]>::into_vec<A>`): the LLBC no longer distinguishes it
  from a phantom parameter, such as the `T` of `size_of<T>`, which is kept.

## Invariants

- Without the flag, the output is byte-identical to upstream's.
- With the flag, no item from a non-local crate is emitted, and the flag is
  rejected for non-Lean backends.
- All Lean overrides from `ExtractBuiltinLean.ml` are disabled except the
  shape-only ones (`Box::new`, the allocator `keep_params` map). The
  backend-independent globals of `builtin_globals` (the integer `MIN`, `MAX`
  and `BITS` constants, `UNIT_METADATA`) stay active.
- The allocator filter never applies to local items, and drops only
  parameters that can be allocators (#77).
- With the default `-use-lean-modules`, `CoreModels` must be a Lean module:
  generated files are modules and `public import CoreModels`.

## Tests

- `tests/src/core-models-lib.rs` (expected output
  `tests/lean/CoreModelsLib/CoreModelsLib.lean`, in a subdirectory so that
  `tests/lean` does not build it): derived `Eq`, `Box::new`, `Vec` methods,
  `callee`/`caller` and a loop with a `C: Op` generic (#75), a local impl of a
  non-local trait, `as_slice`, `[x; N]`, `Some` as a function, and a promoted
  constant, which must be inlined rather than extracted as a global (the
  global filter combines this patch's check with upstream's promoted-constant
  check).
  Also local constants and a local static (extracted as usual), and the
  non-local `u32::MAX` and `usize::BITS`, which must stay mapped to the
  builtin globals `core.num.U32.MAX`/`core.num.Usize.BITS`: if the integer
  `MIN`/`MAX`/`BITS` globals were disabled under the flag, they would become
  monadic reads of unknown globals (checked on 2026-11-02).
- `tests/src/core-models-lib-generics.rs` (expected output
  `tests/lean/CoreModelsLib/CoreModelsLibGenerics.lean`, #77): phantom type
  parameters (`size_of`, `align_of`, `needs_drop`, `iter::empty`) are kept;
  the allocators of `Vec`, `Rc`, `Arc` impls (including `A: Clone` clauses,
  two allocators in `PartialEq`, `IntoIter<T, A>` in the header) and of
  `<[T]>::into_vec<A>` are dropped; `VecDeque`'s allocator, which
  `hide_allocator` does not hide, is kept.

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
- Since upstream #1412, generic parameters are extracted as `Type _`, while
  `CoreModels` uses `Type`. Lean solves the `_` to `Type` from the uses of
  `CoreModels` items, so the generated code stays compatible; only the
  expected output changes.
- On each charon bump, check whether `hide_allocator` still leaves an item's
  own allocator parameter bound and unused (charon's own snapshot
  `charon/tests/ui/issue-165-vec-macro.out` shows
  `pub fn into_vec<T, A>(_1: Box<[T]>) -> Vec<T>`, called as
  `into_vec<i32, Global>`). Not reported upstream as of 2026-11-04 (work.org
  [F24]). Once charon removes these parameters, drop
  `Extract.core_models_fun_allocator_params` and the own-parameter case of
  the allocator filter.

## History

- 2026-10-07: bootstrapped from fork PRs #2, #6, #65, #75; ported to upstream's
  removal of LLBC builtin functions (#1320) and to Lean module-system output
  (#1230); the clause-filter length fix moved to `fix-trait-clause-filter-length`.
- 2026-10-20: the global filter is merged with upstream's promoted-constant
  check (#1404); test for promoted constants added.
- 2026-10-23: the allocator filter keeps the type parameters that are not
  allocators (fork PR #77).
- 2026-11-02: test for constants (local and builtin) under the flag, against
  the charon consts rework (upstream #1471, #1496).
- 2026-11-04: rebased on the 2026-11-02 dev (no change; the
  `core-models-lib-generics` test sits next to the new constants test). An
  item's own parameters are dropped only if listed, instead of whenever its
  signature mentions `Box`/`Vec`/`Rc`/`Arc`.
