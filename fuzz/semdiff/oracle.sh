#!/usr/bin/env bash
# oracle.sh -- full Phase-2 semantic-differential pipeline for ONE Rust crate.
#
#   .rs  --charon-->  .llbc  --aeneas-->  .lean  --lake env lean-->  verdicts
#    |                                                                   ^
#    +------------- rustc (overflow-checks=on) native run ---------------+
#
# This is the reference driver that the fuzz harness can call (or crib from).
# It measures per-crate wall time for each stage.
#
# Usage: oracle.sh SRC.rs [--strict] [--work DIR]
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC=""; STRICT=""; WORK=""
CHARON="${CHARON:-/Users/karthik/charon/charon/target/release/charon}"
AENEAS="${AENEAS:-/Users/karthik/aeneas/bin/aeneas}"
CARGO_BIN="${CARGO_BIN:-/Users/karthik/.cargo/bin}"
ELAN_BIN="${ELAN_BIN:-/Users/karthik/.elan/bin}"

while [ $# -gt 0 ]; do
  case "$1" in
    --strict) STRICT="--strict"; shift;;
    --work) WORK="$2"; shift 2;;
    -*) echo "oracle.sh: unknown arg $1" >&2; exit 2;;
    *) SRC="$1"; shift;;
  esac
done
[ -n "$SRC" ] || { echo "usage: oracle.sh SRC.rs [--strict]" >&2; exit 2; }
SRC="$(cd "$(dirname "$SRC")" && pwd)/$(basename "$SRC")"
base="$(basename "$SRC" .rs)"
WORK="${WORK:-$(mktemp -d "${TMPDIR:-/tmp}/semdiff-oracle.XXXXXX")}"
mkdir -p "$WORK/out"

now() { python3 -c 'import time;print(f"{time.time():.3f}")'; }
t0=$(now)

# 1. charon: Rust -> LLBC
PATH="$ELAN_BIN:$CARGO_BIN:$PATH" "$CHARON" rustc --preset=aeneas \
    --dest-file "$WORK/$base.llbc" -- --crate-type=rlib "$SRC" >/dev/null 2>&1
t1=$(now)

# 2. aeneas: LLBC -> Lean
"$AENEAS" -backend lean -abort-on-error -no-progress-bar \
    "$WORK/$base.llbc" -dest "$WORK/out" >/dev/null 2>&1
t2=$(now)

# 3. native ground truth (overflow-checks ON)
PATH="$CARGO_BIN:$PATH" bash "$HERE/native_run.sh" "$SRC" "$WORK/$base.native.json"
t3=$(now)

# 4. Lean eval + compare
set +e
bash "$HERE/check.sh" --dest "$WORK/out" --native "$WORK/$base.native.json" \
    $STRICT --out "$WORK/$base.verdict.json"
rc=$?
set -e
t4=$(now)

echo "=== verdicts ($base) ==="
cat "$WORK/$base.verdict.json"
echo
printf '=== timings (s): charon=%.2f aeneas=%.2f native=%.2f lean=%.2f total=%.2f ===\n' \
    "$(echo "$t1-$t0"|bc)" "$(echo "$t2-$t1"|bc)" "$(echo "$t3-$t2"|bc)" \
    "$(echo "$t4-$t3"|bc)" "$(echo "$t4-$t0"|bc)"
echo "workdir: $WORK  (exit $rc)"
exit $rc
