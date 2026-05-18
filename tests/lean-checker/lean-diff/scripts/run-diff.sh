#!/usr/bin/env bash
# Lean-side differential harness driver.
#
# Regenerates the Lean fixtures from cert JSON, rebuilds the Lean
# runner exe (against the mathlib-free `RuntimeShim`), builds the
# Rust oracle, runs both, and diffs their stdout.
#
# Exits 0 if and only if the byte streams agree.

set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
repo_root="$(cd "$here/../../.." && pwd)"
aeneas_check="$repo_root/aeneas-lean-checker/.lake/build/bin/aeneas-check"
llbc_dir="$repo_root/tests/llbc"

fixtures=(incr_cert compare_simple calls)

echo "[lean-diff] regenerating Lean fixtures via aeneas-check"
for fx in "${fixtures[@]}"; do
  "$aeneas_check" "$llbc_dir/$fx.cert.json" --out "$here/generated/$fx.lean" \
    | tail -2
done

echo "[lean-diff] building Lean runner (lake build)"
( cd "$here" && lake build )

echo "[lean-diff] building Rust oracle (cargo build --release)"
( cd "$here/rust-runner" && cargo build --release )

lean_out="$(mktemp)"
rust_out="$(mktemp)"
trap 'rm -f "$lean_out" "$rust_out"' EXIT

echo "[lean-diff] running Lean runner"
"$here/.lake/build/bin/leandiff" > "$lean_out"

echo "[lean-diff] running Rust oracle"
"$here/rust-runner/target/release/rust-oracle" > "$rust_out"

lean_lines="$(wc -l < "$lean_out" | tr -d ' ')"
rust_lines="$(wc -l < "$rust_out" | tr -d ' ')"

if diff -u "$lean_out" "$rust_out" > /dev/null; then
  echo "[lean-diff] PASS — $lean_lines Lean lines == $rust_lines Rust lines (byte-identical)"
  exit 0
else
  echo "[lean-diff] FAIL — differential mismatch:"
  diff -u "$lean_out" "$rust_out"
  exit 1
fi
