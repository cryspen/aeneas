#!/usr/bin/env bash
# M9.7m: Cert v3 parity test — translator output diff with both
# settings of `AENEAS_USE_LLBC_PROGRAM` on the full fixture sweep.
#
# For every `tests/llbc/<base>.cert.json`, run aeneas-check twice
# (once with USE_LLBC_PROGRAM=0, once =1) and `diff` the emitted
# Lean source. Divergences are reported with a unified diff.
#
# Fixtures whose cert v2 → v3 regen hasn't landed yet (empty
# `llbcProgram`) silently fall back to the flat path under the
# `=1` setting, producing identical output to `=0`. Those count
# as "pass" — they're not exercising the structured path, but
# they aren't broken either.
#
# `KNOWN_DIVERGENT`: an allow-list of fixtures where the structured
# path produces strictly more accurate output than the flat path's
# opaque-string parser (e.g., propagates a generic type variable into
# a slice element, recognises U128 as the correct integer type,
# unwraps Box transparently in field types). These are documented
# structural improvements; the flat path's output is the legacy
# behaviour that F1's cert regen will replace.
#
# Exit codes:
#   0 → no divergences OUTSIDE the allow-list
#   1 → unexpected divergence (or any aeneas-check failure)

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TESTS="$ROOT/tests"
CHECKER="$ROOT/aeneas-lean-checker"
BIN="$CHECKER/.lake/build/bin/aeneas-check"
AENEAS="$ROOT/bin/aeneas"

REGEN_CERTS="${REGEN_CERTS:-1}"   # set to 0 to skip regen and use on-disk certs

if [[ ! -x "$BIN" ]]; then
  ( cd "$CHECKER" && lake build aeneas-check )
fi
if [[ ! -x "$AENEAS" ]]; then
  ( cd "$ROOT" && gmake build )
fi

# Optional cert regen so the parity test exercises the *current*
# OCaml emitter's LLBC encoding (e.g., array lengths post-M9.7m).
# Skipping it means the parity test reads whatever cert is on disk —
# OK after F1 lands but misleading during E3 development.
if [[ "$REGEN_CERTS" = "1" ]]; then
  echo "  regenerating certs (REGEN_CERTS=0 to skip) ..."
  regen_ok=0; regen_skip=0
  for llbc in "$TESTS"/llbc/*.llbc; do
    [[ -f "$llbc" ]] || continue
    if "$AENEAS" -emit-cert "$llbc" >/dev/null 2>&1; then
      regen_ok=$((regen_ok+1))
    else
      regen_skip=$((regen_skip+1))
    fi
  done
  echo "  regen: $regen_ok ok / $regen_skip skipped"
fi

# M9.7m: known structural improvements where the structured-source
# translator produces strictly more accurate output than the
# flat-source string parser. F1's cert regen will rebaseline these.
KNOWN_DIVERGENT=(
  closures                       # closure-capture field type, Insts naming disambiguator
  constants                      # generic type-var in array element
  issue-804-closure-return-ref   # array field in closure capture
  iterators                      # U128 vs U32 element fallback
  mut-borrow-in-shared-borrow    # propagates Self type-var into Slice elem
  traits                         # WithConstTy.f shape + trait-clause binders on BoolWrapper
)

ok=0
diverge=0
diverge_known=0
errored=0
divergent_fixtures=()
errored_fixtures=()

is_known_divergent() {
  local f="$1"
  for k in "${KNOWN_DIVERGENT[@]}"; do
    [[ "$f" == "$k" ]] && return 0
  done
  return 1
}

tmpdir="$(mktemp -d)"
trap "rm -rf $tmpdir" EXIT

for src in "$TESTS"/src/*.rs; do
  base=$(basename "$src" .rs)
  cert="$TESTS/llbc/${base}.cert.json"
  [[ -f "$cert" ]] || continue

  out_flat="$tmpdir/${base}.flat.lean"
  out_struct="$tmpdir/${base}.struct.lean"

  if ! AENEAS_USE_LLBC_PROGRAM=0 "$BIN" "$cert" --out "$out_flat" >/dev/null 2>&1; then
    errored=$((errored+1))
    errored_fixtures+=("$base (flat)")
    continue
  fi
  if ! AENEAS_USE_LLBC_PROGRAM=1 "$BIN" "$cert" --out "$out_struct" >/dev/null 2>&1; then
    errored=$((errored+1))
    errored_fixtures+=("$base (struct)")
    continue
  fi

  if diff -q "$out_flat" "$out_struct" >/dev/null 2>&1; then
    ok=$((ok+1))
  else
    if is_known_divergent "$base"; then
      diverge_known=$((diverge_known+1))
    else
      diverge=$((diverge+1))
      divergent_fixtures+=("$base")
    fi
  fi
done

echo
echo "=== Cert v3 parity (M9.7m) ==="
echo "  parity OK:        $ok"
echo "  diverged (known): $diverge_known"
echo "  diverged (NEW):   $diverge"
echo "  errored:          $errored"

if (( diverge > 0 )); then
  echo
  echo "=== NEW divergent fixtures (first 20) ==="
  for f in "${divergent_fixtures[@]:0:20}"; do
    echo "  - $f"
    AENEAS_USE_LLBC_PROGRAM=0 "$BIN" "$TESTS/llbc/${f}.cert.json" --out "$tmpdir/${f}.flat.lean" >/dev/null 2>&1 || true
    AENEAS_USE_LLBC_PROGRAM=1 "$BIN" "$TESTS/llbc/${f}.cert.json" --out "$tmpdir/${f}.struct.lean" >/dev/null 2>&1 || true
    diff -u "$tmpdir/${f}.flat.lean" "$tmpdir/${f}.struct.lean" | head -40 || true
    echo "  ---"
  done
fi

if (( errored > 0 )); then
  echo
  echo "=== Errored fixtures ==="
  for f in "${errored_fixtures[@]}"; do
    echo "  - $f"
  done
fi

if (( diverge > 0 || errored > 0 )); then
  exit 1
fi
exit 0
