#!/usr/bin/env bash
# Reproduce the FORK-ONLY closure crash "Internal error: please file an issue"
# at SymbolicToPureValues.ml:366. Upstream translates this fine (exit 0).
set -euo pipefail
cd "$(dirname "$0")"

CHARON="${CHARON_FORK_BIN:-/Users/karthik/charon/charon/target/release/charon}"
AENEAS="${AENEAS_FORK_ROOT:-/Users/karthik/aeneas}/bin/aeneas"

# rustc accepts it (valid Rust):
rustc --edition=2021 -C overflow-checks=on --crate-type=rlib --emit=metadata \
      -o /tmp/closure.rmeta min.rs && echo "rustc: OK"

"$CHARON" rustc --preset=aeneas --dest-file min.llbc -- --crate-type=rlib min.rs
"$AENEAS" -backend lean -abort-on-error -no-progress-bar min.llbc -dest out || \
  echo "aeneas exit: $?  (fork: expected 2 — 'Internal error', SymbolicToPureValues.ml:366)"
