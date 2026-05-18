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

fixtures=(incr_cert compare_simple calls bitwise scalars)

echo "[lean-diff] regenerating Lean fixtures via aeneas-check"
for fx in "${fixtures[@]}"; do
  "$aeneas_check" "$llbc_dir/$fx.cert.json" --out "$here/generated/$fx.lean" \
    | tail -2
done

# Session 7 (Item 2 follow-up): `constants` regen with `use_v` skipped.
# Item 2's generic-globals work emits `V.LEN T N`, but the shim's
# `constants.V.LEN` is a zero-arg `Result Usize` (no type-binders),
# so applying it to `T N` fails to elaborate. Once the shim grows
# the typed `(T : Type) (N : Std.Usize) → Result Std.Usize` form (or
# the emitter learns to drop generic args when calling a non-generic
# shim binding), `use_v` can rejoin the build.
echo "[lean-diff] regenerating constants.lean (with --skip-decl filter)"
"$aeneas_check" "$llbc_dir/constants.cert.json" --out "$here/generated/constants.lean" \
  --skip-decl use_v \
  | tail -2

# Session 5 (Item 2): `demo` regen with the skip list. The 11
# skipped decls each have a documented emit-side gap (see
# `LeanDiff/DemoRunner.lean`'s file-level doc). The 5 well-emitted
# fns are exercised by the runner.
echo "[lean-diff] regenerating demo.lean (with --skip-decl filter)"
"$aeneas_check" "$llbc_dir/demo.cert.json" --out "$here/generated/demo.lean" \
  --skip-decl CList \
  --skip-decl Counter \
  --skip-decl "Std.Usize.Insts.DemoCounter" \
  --skip-decl "Std.Usize.Insts.DemoCounter.incr" \
  --skip-decl choose \
  --skip-decl list_nth \
  --skip-decl list_nth_mut \
  --skip-decl list_tail \
  --skip-decl list_nth1 \
  --skip-decl list_nth1_loop \
  --skip-decl list_nth1_loop.body \
  --skip-decl use_counter \
  --skip-decl i32_id \
  | tail -2

# Session 7 (Item 3): `paper` regen with the skip list. `ref_incr`
# elaborates cleanly; the other decls hit open emit gaps (see
# `LeanDiff/PaperRunner.lean`'s file-level doc).
echo "[lean-diff] regenerating paper.lean (with --skip-decl filter)"
"$aeneas_check" "$llbc_dir/paper.cert.json" --out "$here/generated/paper.lean" \
  --skip-decl List \
  --skip-decl test_incr \
  --skip-decl choose \
  --skip-decl test_choose \
  --skip-decl list_nth_mut \
  --skip-decl sum \
  --skip-decl test_nth \
  --skip-decl call_choose \
  | tail -2

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
