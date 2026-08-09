#!/bin/sh
# Reproducer for the char-match "Inconsistent state" crash.
# Fingerprint: Other  interp/InterpStatements.ml:1100  ("Inconsistent state")
# top frame:   Aeneas__InterpStatements.eval_switch_raw.(fun)
# Reproduces on BOTH targets:
#   fork     (dump-pure-ir-minimal, charon v0.1.196): InterpStatements.ml:1100
#   upstream (main 3a8586fa,        charon v0.1.225): InterpStatements.ml:1132
set -e

CHARON="${CHARON_FORK_BIN:-/Users/karthik/charon/charon/target/release/charon}"
AENEAS="${AENEAS_FORK_ROOT:-/Users/karthik/aeneas}/bin/aeneas"

"$CHARON" rustc --preset=aeneas --dest-file min.llbc -- --crate-type=rlib min.rs
"$AENEAS" -backend lean -abort-on-error -no-progress-bar min.llbc -dest out
