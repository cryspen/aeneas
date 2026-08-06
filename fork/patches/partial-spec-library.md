# partial-spec-library

## Summary

States the panicking operations of the Lean standard library with `partialSpec`
(fork PRs #4, #35): scalar arithmetic, division and remainder, shifts, array
and slice indexing, updates, subslices, `split_at`, and `massert`. Functions
that cannot panic keep their `spec` lemmas.

Some success postconditions also state the no-panic precondition when it does
not follow from the rest (e.g. `Slice.update_spec` gives `i.val < v.length`),
so that partial-correctness proofs can use it. `split_at` uses
`s1.length + n = s.length` instead of truncated subtraction.

The goal is that the success postcondition of every panicking operation implies
its no-panic condition, but the lemmas don't do that yet. Known exceptions:

- `Array.update_spec`, `Array.subslice_spec` and `Array.update_subslice_spec`;
- the `Array.index_*Range*` lemmas, where truncated subtraction (`-`) hides
  ill-formed ranges;
- `div_spec` and `rem_spec`, where `x / 0 = 0` (resp. `x % 0 = x`) on the
  mathematical side, so the result equation does not rule out `y = 0`;
- the shifts by an `IScalar` amount.

## Invariants

- The converted lemmas take no hypotheses; their `.step_spec` carry them.
- The converted lemmas keep upstream's universe-polymorphic binders
  (`{T : Type _}`, upstream #1412).
- Code that names a converted lemma for `step` refers to its `.step_spec`
  (e.g. `step with U32.add_spec.step_spec`).

## Tests

- `backends/lean/Aeneas/Tactic/Step/Tests/PartialSpecLibrary.lean`, including
  `step*` on `split_at` and instantiations at `T := Type` of the lemmas whose
  binders were merged with upstream's `Type _` (with `{T : Type}` they fail).
- The tests of `partial-spec` and the extracted `tests/lean` proofs that use
  `step*` on library operations.

## Rebase notes

- Before `reduce-error-cases`, arithmetic failures are `.integerOverflow`
  (including the shared-reference `add_spec`s). The error kind of `mul` comes
  from `UScalar.tryMk_fail`/`IScalar.tryMk_fail`, so upstream's `mul_equiv`
  is unchanged.

- New upstream code that names a converted lemma breaks without a textual
  conflict: grep upstream's added lines for the converted names (e.g. #1380's
  `Tactic/Step/Tests/HigherOrderOption.lean` used `U32.add_spec`).
- `«%S».mul_spec` is instantiated for every integer type, and `simp_all`
  closes the overflow case for all but `Usize`; the remaining goal is closed
  with `all_goals scalar_tac`, which Lean's unused-tactic linter accepts.

## History

- 2026-10-07: bootstrapped from fork PRs #4 (library part) and #35; ported to
  the ITree-based monad (#1180) and the removal of `spec_imp_exists` (#1353,
  #1384).
- 2026-10-20: merged with upstream's `Type _` binders (#1412); ported to Lean
  v4.35.0 (`«%S».mul_spec`, deprecated `mvcgen` syntax in tests);
  `HigherOrderOption.lean` (#1380) uses `U32.add_spec.step_spec`.
