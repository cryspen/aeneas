#!/usr/bin/env bash
# Regenerate the per-fixture R₂ Rust models that back the diff harness
# in tests/diff.rs.
#
# Pipeline per fixture:
#
#   tests/llbc/<fixture>.llbc
#     -> bin/aeneas -dump-pure-ir pre-extract:<tmp>
#     -> <tmp>/<fixture>.pure.json
#     -> cargo run --bin pir2rs -- <json>
#     -> tests/models/<fixture>_pir.rs
#
# This harness only consumes the *pre-extract* stage (the last Pure-IR
# stage before the OCaml side hands off to LeanEmit). The other two
# stages (`post-s2p`, `post-micro`) are exercised by
# tests/compile_check.rs.
#
# The fixture list is hard-coded below — it must be a subset of the
# "green" fixtures in compile_check.rs::KNOWN_GAPS where the
# pre-extract stage compiles AND every runtime-reachable code path is
# free of `unimplemented!()` / `LoopOp placeholder` panics.
#
# To regenerate: run from the repo root or anywhere — the script
# resolves paths relative to its own location.

set -euo pipefail

# Resolve repo root + paths.
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$CRATE_DIR/../.." && pwd)"
AENEAS="$REPO_ROOT/bin/aeneas"
LLBC_DIR="$REPO_ROOT/tests/llbc"
DEST="$CRATE_DIR/tests/models"

if [[ ! -x "$AENEAS" ]]; then
  echo "error: aeneas binary not found at $AENEAS — run 'make build-bin-dir' from $REPO_ROOT" >&2
  exit 1
fi

mkdir -p "$DEST"

# Fixtures whose pre-extract emit (a) compiles per compile_check and
# (b) has runtime-reachable scalar/ADT paths free of panicking
# placeholders.
FIXTURES=(
  incr_cert
  constants
  bitwise
  compare_simple
  aggregates_basic
  enums_basic
  enums_payload
  traits_basic
  demo
)

# Workspace dir for the pir2rs invocation. Bumping CARGO_TARGET_DIR
# only when unset keeps reusing the workspace's existing target tree
# (so this is fast on repeated runs).
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/rust/target}"

# Build pir2rs once up front so the per-fixture cargo run invocations
# don't each pay the build-script-check overhead.
(
  cd "$REPO_ROOT/rust"
  cargo build -p pure-ir-emit-rust --bin pir2rs --quiet
)

PIR2RS="$CARGO_TARGET_DIR/debug/pir2rs"
if [[ ! -x "$PIR2RS" ]]; then
  echo "error: pir2rs binary not produced at $PIR2RS" >&2
  exit 1
fi

for f in "${FIXTURES[@]}"; do
  llbc="$LLBC_DIR/$f.llbc"
  if [[ ! -f "$llbc" ]]; then
    echo "warn: $llbc missing, skipping $f" >&2
    continue
  fi

  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT

  # Aeneas writes <fixture>.pure.json into the dump dir.
  "$AENEAS" -backend lean -dest "$tmp" \
    -dump-pure-ir "pre-extract:$tmp" \
    "$llbc" >/dev/null 2>&1

  json="$tmp/$f.pure.json"
  if [[ ! -f "$json" ]]; then
    echo "error: aeneas did not emit $json for $f" >&2
    exit 1
  fi

  out="$DEST/${f}_pir.rs"
  raw="$tmp/${f}_pir.raw.rs"
  "$PIR2RS" "$json" -o "$raw"

  # Strip the leading `#![allow(...)]` inner attribute — when this
  # file is `include!`d inside `pub mod <fixture> { ... }`, inner
  # attributes inside a block module are not permitted. The outer
  # `#[allow(...)]` on the wrapping `mod` in `tests/diff.rs` covers
  # the same warning surface.
  awk 'NR==1 && /^#!\[allow\(/ { next } { print }' "$raw" > "$out"
  echo "[regen] wrote $out"

  rm -rf "$tmp"
  trap - EXIT
done

echo
echo "Done. ${#FIXTURES[@]} model file(s) refreshed under $DEST."
