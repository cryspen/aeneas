# reduce-error-cases

## Summary

Reduces the Lean `Error` type to the two cases that behave differently:
`panic` and `undef` (fork PR #44). `integerOverflow`, `divisionByZero`,
`arrayOutOfBounds`, `maximumSizeExceeded` and `assertionFailure` are all
Rust panics. See the Zulip discussion linked in the PR.

The commit is the output of `fork/scripts/reduce-error-cases.py`, followed by
`reduce-error-cases.py --fix-guard-msgs` (which re-wraps `#guard_msgs`
expectations; it needs a built `backends/lean`).

## Invariants

- `Error` has exactly the constructors `panic` and `undef`.
- No source mentions the removed constructor names.
- `error_pred_eq_disj` (see `partial-spec`) enumerates exactly the kept
  constructors.

## Tests

- The library and its tests, `tests/lean`.

## Rebase notes

- Regenerate the commit with the script; never resolve its conflicts. It must
  come after `partial-spec` and `partial-spec-library`: it anchors on
  `theorem error_pred_eq_disj` and merges colliding `fun | …` arms.
- The script's leftover check skips `fork/` (whose files name the removed
  constructors).
- The script does not remove `| _ => False` arms that become redundant:
  `Tactic/Step/Tests/SpecPartial.lean`'s `myCheck_partialSpec` (which lists
  `.panic` and `.undef`) is edited by hand in this commit.

## History

- 2026-10-07: bootstrapped from fork PR #44; the script (from the gist linked in
  the PR) is checked in.
