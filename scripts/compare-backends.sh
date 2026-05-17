#!/usr/bin/env bash
# Side-by-side comparison of `aeneas -backend lean` (standard) and
# `aeneas-check` (new cert-based) output for a Rust input.
#
# Usage: scripts/compare-backends.sh <tests/src/foo.rs>

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="${1:?usage: $0 <tests/src/foo.rs>}"

if [[ ! -f "$SRC" ]]; then
    echo "no such file: $SRC" >&2
    exit 1
fi

base=$(basename "$SRC" .rs)
LLBC="$ROOT/tests/llbc/${base}.llbc"
STD_OUT="/tmp/aeneas_compare/${base}-standard"
NEW_OUT="/tmp/aeneas_compare/${base}-checker.lean"
CHARON="${CHARON:-/Users/karthik/charon/charon/target/release/charon}"

mkdir -p "$STD_OUT" "$(dirname "$NEW_OUT")"

echo "==> charon rustc"
"$CHARON" rustc --preset=aeneas --dest-file="$LLBC" -- "$SRC" --crate-type=lib

echo "==> aeneas -emit-cert (new pipeline)"
"$ROOT/bin/aeneas" -emit-cert "$LLBC" >/dev/null

echo "==> aeneas -backend lean (standard pipeline)"
"$ROOT/bin/aeneas" -backend lean -dest "$STD_OUT" "$LLBC" 2>&1 | grep -E "(Generated|Error)" || true

echo "==> aeneas-check --out (new pipeline)"
"$ROOT/aeneas-lean-checker/.lake/build/bin/aeneas-check" \
    "$ROOT/tests/llbc/${base}.cert.json" \
    --out "$NEW_OUT" >/dev/null

# Find the file the standard backend produced.
std_file=$(find "$STD_OUT" -name "*.lean" | head -1)

echo
echo "─── Standard backend ($(basename "$std_file")) ───"
cat "$std_file"
echo
echo "─── New checker backend (${base}-checker.lean) ───"
cat "$NEW_OUT"
echo
echo "─── diff (standard → checker) ───"
diff -u "$std_file" "$NEW_OUT" || true
