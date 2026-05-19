#!/usr/bin/env bash
# Regenerate stripped mirrors of fixture sources under
# `tests/lean-checker/differential/src/fixtures/`.
#
# Four `tests/src/*.rs` fixtures use crate-level inner attributes
# (`#![feature(register_tool)]` + `#![register_tool(verify)]`) and
# `#[verify::test]` annotations to drive charon's verify-tooling. These
# inner attrs can't appear in a `#[path]`-included module, so the
# meta-harness `--generate-tests` pre-scan uses a stripped mirror
# instead. This script regenerates those mirrors from the canonical
# `tests/src/*.rs` originals.
#
# Charon and the cert pipeline continue to consume the originals; only
# the differential proptest crate touches the mirrors.

set -euo pipefail

cd "$(dirname "$0")/.."

FIXTURES=(chunks_exact paper no_nested_borrows step_by)
OUT_DIR="tests/lean-checker/differential/src/fixtures"
mkdir -p "$OUT_DIR"

for fx in "${FIXTURES[@]}"; do
  src="tests/src/$fx.rs"
  dst="$OUT_DIR/$fx.rs"
  if [[ ! -f "$src" ]]; then
    echo "regen-fixture-mirrors: missing source $src" >&2
    exit 1
  fi
  {
    cat <<EOF
// AUTO-GENERATED stripped mirror of $src.
//
// The original file uses charon-verify tooling via crate-level inner
// attributes and per-fn verify-test annotations; those inner attrs
// can't appear in a path-included module, so the meta-harness
// pre-scan in tools/meta-harness/src/generate.rs uses this stripped
// mirror instead. The non-test definitions are byte-for-byte
// identical to the original (only the offending attrs are removed).
//
// Regen: scripts/regen-fixture-mirrors.sh

EOF
    # Strip:
    #   * the two crate-level inner attrs (rustc bans inner attrs in
    #     `#[path]`-included modules);
    #   * `#[verify::test]` markers (the `verify` tool isn't registered);
    #   * specific fns that panic/unreachable on truthy bool inputs
    #     (proptest treats Rust-side panics as test failures even when
    #     the model agrees; the candidate filter in meta-harness sees
    #     the absent body and emits a SKIPPED comment instead).
    awk '
      BEGIN { skip_fn = 0; brace = 0; seen_open = 0 }
      /^#!\[feature\(register_tool\)\]$/ { next }
      /^#!\[register_tool\(verify\)\]$/ { next }
      /^[[:space:]]*#\[verify::test\][[:space:]]*$/ { next }
      !skip_fn && /^pub fn (test_unreachable|test_panic|test_panic_msg)\(/ {
        skip_fn = 1; brace = 0; seen_open = 0
      }
      skip_fn {
        opens = 0; closes = 0
        s = $0
        for (i = 1; i <= length(s); i++) {
          ch = substr(s, i, 1)
          if (ch == "{") opens++
          if (ch == "}") closes++
        }
        if (opens > 0) seen_open = 1
        brace += opens - closes
        if (seen_open && brace == 0) { skip_fn = 0 }
        next
      }
      { print }
    ' "$src"
  } > "$dst"
  echo "regen-fixture-mirrors: wrote $dst ($(wc -l < "$dst") lines)"
done
