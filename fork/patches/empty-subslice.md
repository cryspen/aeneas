# empty-subslice

## Summary

Rust allows empty subranges, including `s[s.len()..s.len()]`, but the Lean
models of `Slice.subslice`, `Slice.update_subslice`, `Array.subslice` and
`Array.update_subslice` required `start < end`. They now require
`start ≤ end` (fork PR #30). Suitable for upstream.

## Invariants

- `subslice` succeeds iff `start ≤ end ≤ len`; `update_subslice` additionally
  requires the inserted slice to have length `end - start`.

## Tests

- `backends/lean/Aeneas/Tactic/Step/Tests/EmptySubslice.lean`.

## History

- 2026-10-07: bootstrapped from fork PR #30.
