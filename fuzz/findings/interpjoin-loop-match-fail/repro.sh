#!/usr/bin/env bash
# Reproduce the loop fixed-point join crash "Could not match the contexts".
# Reproduces on BOTH targets (fork: InterpJoin.ml:1515, upstream: :1542).
# For upstream, set CHARON/AENEAS to the upstream binaries (see
# fuzz/targets/upstream.toml) and add --allow=unused --edition=2021 to charon.
set -euo pipefail
cd "$(dirname "$0")"

CHARON="${CHARON_FORK_BIN:-/Users/karthik/charon/charon/target/release/charon}"
AENEAS="${AENEAS_FORK_ROOT:-/Users/karthik/aeneas}/bin/aeneas"

# rustc accepts it (valid Rust):
rustc --edition=2021 -C overflow-checks=on --crate-type=rlib --emit=metadata \
      -o /tmp/join.rmeta min.rs && echo "rustc: OK"

"$CHARON" rustc --preset=aeneas --dest-file min.llbc -- --crate-type=rlib min.rs
"$AENEAS" -backend lean -abort-on-error -no-progress-bar min.llbc -dest out || \
  echo "aeneas exit: $?  (expected 2 — 'Could not match the contexts', InterpJoin.ml:1515)"
