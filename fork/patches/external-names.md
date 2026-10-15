# external-names

## Summary

Names provided by the backend rather than defined in the crate are called
*external* names (fork PRs #38, #42, #45). Two commits:

1. a refactor: the `builtin_*` information and functions are renamed to
   `external_*`, and the name tables move to `src/extract/ExternalNames.ml`;
2. `-external-names file.json` registers extra external names from JSON files,
   so that their items are not emitted as axioms; the JSON written by
   `-emit-json` can be re-imported (new fields `extract_name`,
   `rust_pattern`), which plugs extractions of several crates together.

## Invariants

- Without `-external-names`, the output is identical to the output without
  this patch.
- A Rust pattern may be mapped only once across all sources (the shipped
  entries and every `-external-names` file): a second entry is an error, as is
  mapping a local, non-opaque item. *(The `-external-names` help text in
  `src/Main.ml`, the documentation of `Config.ml`'s list of files and a comment
  in `ExternalNames.ml` still speak of later files taking precedence; the code
  refuses the run instead.)*
- Exported JSON can be re-imported; loop functions are exported (with a
  `loop` key) and skipped on import.
- The external-name maps are complete before any parallel work starts.

## Tests

- `tests/src/external-names*.rs` with `tests/external-names/*.json`
  (`tests/lean/ExternalNames*`), and `tests/src/roundtrip-lib`/`roundtrip-user`
  (`tests/lean/Roundtrip*`).

## Rebase notes

- Depends on `core-models-lib` (`external_types_keep_params_map`) and on
  `extra-includes` (used by its tests).
- Upstream code added after the refactor that still uses the old `builtin_*`
  names must be renamed too (e.g. #1131's trait-method filter, which reads
  `builtin_info`, and `compute_back_fun_name`, which calls
  `ExtractBuiltin.builtin_funs_map`).
- The hand-written Lean files the tests import (`tests/lean/ExternalNamesModel.lean`,
  the `tests/lean/RoundtripLib.lean` aggregator) must be modules: generated files
  `public import` them.

## History

- 2026-10-07: bootstrapped from fork PRs #38, #42, #45; ported to upstream's
  removal of LLBC builtin functions (#1320) and `-filter-trait-methods` (#1131).
