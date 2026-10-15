# fix-trait-clause-filter-length

## Summary

`fun_builtin_filter_types_trait_clauses` (`src/extract/Extract.ml`) checks that
a function's trait-clause filter has one entry per trait clause. It compared the
filter's length with the number of *type arguments* instead, so a filter of the
right length was rejected (or `List.combine` raised) whenever a function has a
different number of type parameters and trait clauses.

Every builtin clause filter upstream happens to have as many trait clauses as
type parameters, so the bug is latent there. The fork's `-core-models-lib`
allocator filter (see `core-models-lib`) triggers it, e.g. on `Vec` methods
(type parameters `T, A`, trait clause `A: Allocator`). Suitable for upstream.

## Invariants

- The trait-clause filter's length is compared with the number of trait
  clauses, and the type-argument filter's length with the number of type
  arguments.

## Tests

- No standalone test: no upstream builtin has mismatching counts. Covered by
  `tests/src/core-models-lib.rs` (`vec_push`, `vec_sum`) of `core-models-lib`:
  with the fix reverted, its extraction fails with "Ill-formed builtin
  information for function alloc::vec::{alloc::vec::Vec<T>}::push" (checked on
  2026-10-07).

## History

- 2026-10-07: split out of the `core-models-lib` patch (fork PR #2).
