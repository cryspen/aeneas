#!/usr/bin/env bash
# check.sh -- Phase-2 semdiff oracle, LEAN side + comparison.
#
# Given an Aeneas `-dest` directory (or a single generated .lean file) and a
# native-run result JSON (from native_run.sh), evaluate every test function in
# Lean and emit per-test verdicts.
#
# Usage:
#   check.sh --dest DIR        --native NATIVE.json [opts]
#   check.sh --lean-file F.lean --native NATIVE.json [opts]
# Options:
#   --driver DIR   the prebuilt lean-driver lake project (default: alongside)
#   --prefix P     only run defs whose name starts with P (default: test)
#   --strict       also require failure KIND to match (not just OK-vs-FAIL)
#   --out FILE     write the JSON verdict report here (default: stdout)
#   --keep         keep the generated Driver.lean / lean.txt for inspection
#
# Exit code: 0 if no MISMATCH, 1 if a semantic divergence was found, 2 on error.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEST=""; LEAN_FILE=""; NATIVE=""; DRIVER="$HERE/lean-driver"
PREFIX="test"; STRICT=""; OUT="/dev/stdout"; KEEP=""
ELAN_BIN="${ELAN_BIN:-/Users/karthik/.elan/bin}"

while [ $# -gt 0 ]; do
  case "$1" in
    --dest) DEST="$2"; shift 2;;
    --lean-file) LEAN_FILE="$2"; shift 2;;
    --native) NATIVE="$2"; shift 2;;
    --driver) DRIVER="$2"; shift 2;;
    --prefix) PREFIX="$2"; shift 2;;
    --strict) STRICT="--strict"; shift;;
    --out) OUT="$2"; shift 2;;
    --keep) KEEP=1; shift;;
    *) echo "check.sh: unknown arg $1" >&2; exit 2;;
  esac
done

[ -n "$NATIVE" ] || { echo "check.sh: --native required" >&2; exit 2; }

# Resolve the Aeneas-generated Lean file.
if [ -z "$LEAN_FILE" ]; then
  [ -n "$DEST" ] || { echo "check.sh: --dest or --lean-file required" >&2; exit 2; }
  # Pick the .lean file that declares a `namespace` (the crate module).
  LEAN_FILE=""
  for f in "$DEST"/*.lean; do
    [ -e "$f" ] || continue
    if grep -q '^namespace ' "$f"; then LEAN_FILE="$f"; break; fi
  done
  [ -n "$LEAN_FILE" ] || { echo "check.sh: no crate .lean with a namespace in $DEST" >&2; exit 2; }
fi

export PATH="$ELAN_BIN:$PATH"

# Best-effort timeout so a non-terminating test (`loop`/`while true`) cannot
# hang the interpreter forever. Uses coreutils `timeout`/`gtimeout` if present.
LEAN_TIMEOUT="${SEMDIFF_LEAN_TIMEOUT:-120}"
TIMEOUT=""
if command -v timeout >/dev/null 2>&1; then TIMEOUT="timeout $LEAN_TIMEOUT";
elif command -v gtimeout >/dev/null 2>&1; then TIMEOUT="gtimeout $LEAN_TIMEOUT"; fi

# 1. Generate the driver file into the prebuilt lake project.
#    gen_driver writes the list of emitted test defs ("tests: ...") on stderr;
#    capture it so check.py can tell noncomputable evals from absent defs.
python3 "$HERE/gen_driver.py" "$LEAN_FILE" --prefix "$PREFIX" \
    > "$DRIVER/Driver.lean" 2> "$DRIVER/.driver.tests"

# 2. Evaluate in Lean against the prebuilt Aeneas backend (no lake build!).
LEAN_TXT="$(mktemp "${TMPDIR:-/tmp}/semdiff-lean.XXXXXX")"
( cd "$DRIVER" && $TIMEOUT lake env lean Driver.lean ) \
    | grep '^SEMDIFF|' > "$LEAN_TXT" || true

# 3. Join with native ground truth -> verdicts.
set +e
python3 "$HERE/check.py" "$NATIVE" "$LEAN_TXT" $STRICT \
    --expected "$DRIVER/.driver.tests" > "$OUT"
rc=$?
set -e

if [ -z "$KEEP" ]; then rm -f "$LEAN_TXT"; else echo "kept: $DRIVER/Driver.lean $LEAN_TXT" >&2; fi
exit $rc
