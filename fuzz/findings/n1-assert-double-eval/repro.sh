#!/usr/bin/env bash
# Reproduce the "no bottoms" assert double-evaluation crash on the fork binary.
# Adjust CHARON/AENEAS for the upstream target (see fuzz/targets/upstream.toml).
set -euo pipefail
cd "$(dirname "$0")"

CHARON="${CHARON_FORK_BIN:-/Users/karthik/charon/charon/target/release/charon}"
AENEAS="${AENEAS_FORK_ROOT:-/Users/karthik/aeneas}/bin/aeneas"

# rustc accepts it (valid Rust):
rustc --edition=2021 -C overflow-checks=on --crate-type=rlib --emit=metadata \
      -o /tmp/n1.rmeta min.rs && echo "rustc: OK"

"$CHARON" rustc --preset=aeneas --dest-file min.llbc -- --crate-type=rlib min.rs
"$AENEAS" -backend lean -abort-on-error -no-progress-bar min.llbc -dest out || \
  echo "aeneas exit: $?  (expected 2 — 'There should be no bottoms in the value', InterpExpressions.ml:55)"
