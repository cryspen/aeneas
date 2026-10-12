# ci-lean-iofail

## Summary

CI builds the Lean library with `lake build --iofail`, so any warning or info
message fails the build (fork PR #33). Upstream builds it with `--wfail`
(warnings only) since #1476; the patch turns that step's `--wfail` into
`--iofail`.

## Invariants

- Building `backends/lean` produces no messages.

## Tests

- CI itself.

## Rebase notes

- The patch only changes CI. If upstream starts emitting warnings or info
  messages, fixing them in the library belongs in this patch; none were
  needed on 2026-10-07.
- Drop this patch if upstream's Lean build step switches to `--iofail`.

## History

- 2026-10-07: bootstrapped from the CI part of fork PR #33.
- 2026-11-02: shrunk to a one-word change of upstream's new `--wfail` step
  (#1476), which builds the same default targets; the fork's own
  `lake build --iofail` before `tests/lean` is gone.
