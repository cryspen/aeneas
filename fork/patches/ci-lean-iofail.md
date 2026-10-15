# ci-lean-iofail

## Summary

CI builds the Lean library with `lake build --iofail`, so any warning or info
message fails the build (fork PR #33).

## Invariants

- Building `backends/lean` produces no messages.

## Tests

- CI itself.

## Rebase notes

- The patch only changes CI. If upstream starts emitting warnings, fixing them
  in the library belongs in this patch; none were needed on 2026-10-07.

## History

- 2026-10-07: bootstrapped from the CI part of fork PR #33.
