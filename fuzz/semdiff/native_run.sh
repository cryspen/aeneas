#!/usr/bin/env bash
# native_run.sh -- Phase-2 semantic-differential oracle: NATIVE ground truth.
#
# Runs each niladic `pub fn test_*()` from a Rust source natively, catching
# panics, and emits a JSON array of per-test verdicts on stdout.
#
# IMPORTANT: compiled with `-C overflow-checks=on` so that checked integer
# arithmetic (a + b without wrapping_*) PANICS on overflow, matching Aeneas's
# fallible semantics in Lean. Release mode alone would silently wrap and hide
# the discrepancy the oracle is meant to catch.
#
# Usage:
#   native_run.sh SRC.rs [OUT.json]
# Emits JSON to OUT.json (or stdout if omitted). Each element:
#   { "name": "...", "status": "OK"|"PANIC", "kind": "...", "msg": "..." }
# where kind classifies the panic to line up with Aeneas Error variants:
#   ok | assertionFailure | integerOverflow | divisionByZero
#   | arrayOutOfBounds | panic
set -euo pipefail

SRC="${1:?usage: native_run.sh SRC.rs [OUT.json]}"
OUT="${2:-/dev/stdout}"
SRC="$(cd "$(dirname "$SRC")" && pwd)/$(basename "$SRC")"

WORK="$(mktemp -d "${TMPDIR:-/tmp}/semdiff-native.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

# Collect niladic `pub fn test_*()` names (no arguments between the parens).
# Matches `pub fn NAME()` optionally with a return type; skips fns with args.
FNS=()
while IFS= read -r fn; do
  [ -n "$fn" ] && FNS+=("$fn")
done < <(grep -oE 'pub fn[[:space:]]+[A-Za-z0-9_]+[[:space:]]*\([[:space:]]*\)' "$SRC" \
         | sed -E 's/pub fn[[:space:]]+([A-Za-z0-9_]+).*/\1/')

if [ "${#FNS[@]}" -eq 0 ]; then
  echo "[]" > "$OUT"
  echo "native_run: no niladic 'pub fn NAME()' found in $SRC" >&2
  exit 0
fi

# Build a runner crate that includes the source as a module and calls each
# test under catch_unwind. Panic hook is silenced so panic backtraces don't
# pollute stderr; we recover the message from the caught payload.
# Sanitize the source for a *stable* rustc: strip the nightly-only crate
# attributes and the `#[verify::...]` tool attributes that only charon/aeneas
# understand. These are irrelevant to native execution.
python3 - "$SRC" "$WORK/tested.rs" <<'PY'
import re, sys
src, dst = sys.argv[1], sys.argv[2]
out = []
for line in open(src):
    s = line.strip()
    # Drop ALL crate-level inner attributes (#![...]) -- they are illegal
    # inside the `mod tested { ... }` we wrap the source in.
    if s.startswith('#!['):
        continue
    if re.match(r'#\[\s*verify::', s):
        continue
    out.append(line)
open(dst, 'w').write(''.join(out))
PY

{
  # Allow the const-eval panic lints so that OOB indexing, division by zero,
  # and overflow on *constant* operands become RUNTIME panics (caught by
  # catch_unwind) instead of compile-time `deny`d errors.
  echo '#![allow(dead_code, unused_imports, unused_variables)]'
  echo '#![allow(arithmetic_overflow, unconditional_panic)]'
  echo 'mod tested { include!("TESTED_PATH"); }'
  echo 'use std::panic::{catch_unwind, AssertUnwindSafe, set_hook, take_hook};'
  echo 'fn kind_of(msg: &str) -> &'"'"'static str {'
  echo '    if msg.contains("overflow") { "integerOverflow" }'
  echo '    else if msg.contains("divide by zero") || msg.contains("remainder with a divisor of zero") { "divisionByZero" }'
  echo '    else if msg.contains("index out of bounds") || msg.contains("range end index") || msg.contains("range start index") { "arrayOutOfBounds" }'
  echo '    else if msg.starts_with("assertion") { "assertionFailure" }'
  echo '    else { "panic" }'
  echo '}'
  echo 'fn run<F: FnOnce()>(name: &str, f: F, first: &mut bool) {'
  echo '    let r = catch_unwind(AssertUnwindSafe(f));'
  echo '    let (status, kind, msg) = match r {'
  echo '        Ok(()) => ("OK", "ok", String::new()),'
  echo '        Err(e) => {'
  echo '            let m = if let Some(s) = e.downcast_ref::<&str>() { s.to_string() }'
  echo '                    else if let Some(s) = e.downcast_ref::<String>() { s.clone() }'
  echo '                    else { "<non-string panic>".to_string() };'
  echo '            ("PANIC", kind_of(&m), m)'
  echo '        }'
  echo '    };'
  echo '    let esc = |s: &str| s.replace('"'"'\\'"'"', "\\\\").replace('"'"'"'"'"', "\\\"").replace('"'"'\n'"'"', " ");'
  echo '    if !*first { print!(",\n"); } *first = false;'
  echo '    print!("  {{\"name\":\"{}\",\"status\":\"{}\",\"kind\":\"{}\",\"msg\":\"{}\"}}", esc(name), status, kind, esc(&msg));'
  echo '}'
  echo 'fn main() {'
  echo '    set_hook(Box::new(|_| {}));'
  echo '    let mut first = true;'
  echo '    print!("[\n");'
  for fn in "${FNS[@]}"; do
    # Wrap the call; `let _ =` swallows any (possibly non-unit) return value.
    echo "    run(\"$fn\", || { let _ = tested::$fn(); }, &mut first);"
  done
  echo '    print!("\n]\n");'
  echo '    let _ = take_hook();'
  echo '}'
} > "$WORK/main.rs"

# Point the include! at the sanitized copy.
python3 - "$WORK/main.rs" "$WORK/tested.rs" <<'PY'
import sys
p, tested = sys.argv[1], sys.argv[2]
data = open(p).read().replace("TESTED_PATH", tested)
open(p, "w").write(data)
PY

# Compile with overflow checks ON so checked arithmetic panics like Aeneas.
# This is REQUIRED for the oracle: release-mode rustc silently WRAPS on
# overflow, which would make `a + b` look like OK natively while Aeneas models
# it as `fail integerOverflow` -- a spurious MISMATCH. Set
# SEMDIFF_OVERFLOW_CHECKS=off only to demonstrate that divergence.
OVF="${SEMDIFF_OVERFLOW_CHECKS:-on}"
rustc --edition=2021 -C overflow-checks="$OVF" -C debug-assertions=on \
      -o "$WORK/runner" "$WORK/main.rs" 2>"$WORK/rustc.err" || {
  echo "native_run: rustc failed:" >&2; cat "$WORK/rustc.err" >&2; exit 1; }

# Best-effort timeout: a non-terminating test would otherwise hang forever.
NATIVE_TIMEOUT="${SEMDIFF_NATIVE_TIMEOUT:-60}"
if command -v timeout >/dev/null 2>&1; then
  timeout "$NATIVE_TIMEOUT" "$WORK/runner" > "$OUT"
elif command -v gtimeout >/dev/null 2>&1; then
  gtimeout "$NATIVE_TIMEOUT" "$WORK/runner" > "$OUT"
else
  "$WORK/runner" > "$OUT"
fi
