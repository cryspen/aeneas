# extra-includes

## Summary

`-extra-includes=Foo,Bar` adds `import Foo` and `import Bar` to every generated
file (fork PR #36), for multi-crate support: the extraction of other crates is
imported this way.

## Invariants

- Extra includes are emitted exactly like the generated includes (same
  keyword, after them), in every generated file, including spec, obligation
  and template files.
- With the default `-use-lean-modules`, the included files must be Lean
  modules (`public import`).
- Without the option, the output is unchanged.

## Tests

- `tests/src/extra-includes.rs` (`tests/lean/ExtraIncludes`).

## History

- 2026-10-07: bootstrapped from fork PR #36; includes are emitted as
  `public import` since the module system (#1230).
