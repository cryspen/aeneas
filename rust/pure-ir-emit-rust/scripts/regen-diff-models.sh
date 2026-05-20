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

set -uo pipefail
# Deliberately NOT setting `-e` for the whole script: the FIXTURES
# list (~72 fixtures, all "green at pre-extract" per compile_check.rs)
# may carry the occasional fixture whose emit script-line errors out
# in isolation even though the compile-check sweep passes. We log and
# continue; the gen-diff-tests pass then filters by the surviving
# models on disk.

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

# Fixtures whose pre-extract emit compiles per `compile_check.rs`
# (i.e. everything NOT listed under `KNOWN_GAPS` for the
# `pre-extract` stage). Auto-generated `tests/diff_auto.rs` is
# downstream of this list; the gen-diff-tests pass further filters
# by per-fn signature amenability and per-fn body-content
# (skipping `loop_op` / `unimplemented!()` models at runtime).
FIXTURES=(
  adt
  aggregates_basic
  array_slice_index
  arrays_defs
  as_mut
  assert-cfg
  bitwise
  blanket_impl
  builtin
  builtin-auto
  calls
  chunks_exact
  compare_simple
  const-shadow
  constants
  constants-lean
  curve25519
  default
  defaulted_method
  demo
  deref
  derive
  discriminant
  dynamic_size
  enums_basic
  enums_payload
  from_to
  generics_basic
  incr_cert
  into
  issue-134-loop-shared-borrows
  issue-194-recursive-struct-projector
  issue-270-loop-list
  issue-789-loop-ctx-match
  issue-807-missing-symbolic-value
  issue-815-global-referencing-fallible-global
  iterators
  iterators-array
  iterators-scalar
  join-duplicate
  joins
  list_basic
  list_generic
  loop_shared_loan_in_join
  loops
  loops_simple
  loops-issues
  loops-nested
  loops-nested-rec
  loops-rec
  loops-sequences
  mini_tree
  multi_region
  multi-target
  mutually-recursive-traits
  names
  options
  paper
  print
  range
  raw_pointers
  reborrows
  rename_attribute
  scalars
  slices
  slices_basic
  static
  step_by
  string-chars
  switch_test
  traits_basic
  vec
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

written=0
failed_fixtures=()
for f in "${FIXTURES[@]}"; do
  llbc="$LLBC_DIR/$f.llbc"
  if [[ ! -f "$llbc" ]]; then
    echo "warn: $llbc missing, skipping $f" >&2
    failed_fixtures+=("$f")
    continue
  fi

  tmp="$(mktemp -d)"

  # Aeneas writes <fixture>.pure.json into the dump dir. The dump dir
  # must exist (aeneas refuses to create the -dest tree).
  mkdir -p "$tmp"
  if ! "$AENEAS" -backend lean -dest "$tmp" \
        -dump-pure-ir "pre-extract:$tmp" \
        "$llbc" >/dev/null 2>&1; then
    echo "warn: aeneas dump failed for $f" >&2
    failed_fixtures+=("$f")
    rm -rf "$tmp"
    continue
  fi

  json="$tmp/$f.pure.json"
  if [[ ! -f "$json" ]]; then
    echo "warn: no JSON produced for $f" >&2
    failed_fixtures+=("$f")
    rm -rf "$tmp"
    continue
  fi

  out="$DEST/${f}_pir.rs"
  raw="$tmp/${f}_pir.raw.rs"
  if ! "$PIR2RS" "$json" -o "$raw" 2>/dev/null; then
    echo "warn: pir2rs failed for $f" >&2
    failed_fixtures+=("$f")
    rm -rf "$tmp"
    continue
  fi

  # Strip the leading `#![allow(...)]` inner attribute — when this
  # file is `include!`d inside `pub mod <fixture> { ... }`, inner
  # attributes inside a block module are not permitted. The outer
  # `#[allow(...)]` on the wrapping `mod` in `tests/diff.rs` covers
  # the same warning surface.
  awk 'NR==1 && /^#!\[allow\(/ { next } { print }' "$raw" > "$out"
  written=$((written + 1))
  rm -rf "$tmp"
done

echo
echo "Done. $written/${#FIXTURES[@]} model file(s) refreshed under $DEST."
if (( ${#failed_fixtures[@]} > 0 )); then
  echo "Skipped fixtures (no model produced): ${failed_fixtures[*]}"
fi

# Auto-generate `tests/diff_auto.rs` + `tests/common/ref_impl_auto.rs`
# from the surviving models. The generator filters per-fn by signature
# amenability; the surviving fixtures here are the input set.
echo
echo "[regen] running gen-diff-tests..."
(
  cd "$REPO_ROOT/rust"
  cargo run -p pure-ir-emit-rust --bin gen-diff-tests --quiet
)
