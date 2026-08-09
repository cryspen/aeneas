#!/usr/bin/env bash
# Demonstrate the MIN % -1 unsoundness via the semantic differential.
# Native (overflow-checks=on) panics; the Aeneas Lean model evaluates to ok 0.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)/fuzz"
harness/target/release/aeneas-fuzz semdiff \
  --target targets/fork.toml \
  --input findings/n5-rem-min-overflow/min.rs \
  --work /tmp/n5-repro/work --findings /tmp/n5-repro/findings
# Expect: "MISMATCH test_rem_min ... native=...integerOverflow...PANIC lean=OK"
#         "MATCH test_rem_ok"
