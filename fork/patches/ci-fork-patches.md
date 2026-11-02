# ci-fork-patches

## Summary

CI checks that every commit of a pull request belongs to a documented fork
patch (issue #88): the `fork patches` workflow runs
`scripts/ci-check-fork-patches.sh` on the pull request's commits, minus those
that come from upstream's `main`.

## Invariants

- Each checked commit carries exactly one `Fork-Patch: <name>` trailer.
- `fork/patches/<name>.md` exists at the head of the pull request.
- Each checked commit modifies `fork/patches/<name>.md` or a
  `fork/scripts/<name>.*` script.

## Tests

- CI itself; locally, `scripts/ci-check-fork-patches.sh BASE..HEAD`.

## Rebase notes

- The patch only adds files, so it should not conflict with upstream.
- The first commit of `external-names` (the `ExternalNames` refactor) does not
  modify `fork/` and would fail the check if a pull request contains it.

## History

- 2026-11-01: added (issue #88).
