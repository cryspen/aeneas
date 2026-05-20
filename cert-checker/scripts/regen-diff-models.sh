#!/usr/bin/env bash
# Regenerate cert.json and Rust model files for every fixture used by
# the differential proptest harness (tests/lean-checker/differential).
#
# Pipeline per fixture:
#
#   tests/src/<fixture>.rs
#     -> charon rustc -> tests/llbc/<fixture>.llbc
#     -> aeneas -emit-cert -> tests/llbc/<fixture>.cert.json
#     -> aeneas-check --rust-model -> /tmp/<fixture>_model.rs
#
# The final model files are *not* concatenated automatically — names
# collide across fixtures and the hand-curated `src/model.rs` block
# encodes the reconciliation. After running this script, diff each
# `/tmp/<fixture>_model.rs` against the corresponding `// ---- <fix>
# ----` block in `tests/lean-checker/differential/src/model.rs`.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BUNDLE="$ROOT/cert-checker"
TESTS="$ROOT/tests"
CHECKER="$BUNDLE/aeneas-lean-checker"
AENEAS="$ROOT/bin/aeneas"
CHARON="${CHARON:-/Users/karthik/charon/charon/target/release/charon}"

FIXTURES=(incr_cert constants bitwise calls compare_simple)

for f in "${FIXTURES[@]}"; do
  echo "[regen] $f"
  "$CHARON" rustc --preset=aeneas \
      --dest-file="$TESTS/llbc/$f.llbc" \
      -- "$TESTS/src/$f.rs" --crate-type=lib >/dev/null
  "$AENEAS" -emit-cert "$TESTS/llbc/$f.llbc" 2>&1 \
    | grep -E "Wrote certificate|borrow-checked" || true
  "$CHECKER/.lake/build/bin/aeneas-check" \
      "$TESTS/llbc/$f.cert.json" \
      --rust-model "/tmp/${f}_model.rs" 2>&1 \
    | grep -E "wrote Rust model" || true
done

echo
echo "Per-fixture model files written to /tmp/<fixture>_model.rs."
echo "Reconcile into tests/lean-checker/differential/src/model.rs"
echo "(the harness file applies <crate>_<fn>_model renames to avoid"
echo "name collisions across fixtures)."
