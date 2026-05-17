#!/usr/bin/env bash
# End-to-end M2-M8 verification: Rust source → cert.json → Lean check
# → Pure IR → Rust model → cargo test passes on random inputs.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TESTS="$ROOT/tests"
CHECKER="$ROOT/aeneas-lean-checker"
DIFF="$TESTS/lean-checker/differential"
AENEAS="$ROOT/bin/aeneas"
CHARON="${CHARON:-/Users/karthik/charon/charon/target/release/charon}"

# 1. Charon: Rust → LLBC
echo "[1/6] charon rustc ..."
"$CHARON" rustc --preset=aeneas \
    --dest-file="$TESTS/llbc/incr_cert.llbc" \
    -- "$TESTS/src/incr_cert.rs" --crate-type=lib

# 2. Aeneas: LLBC → cert.json (cert_fmt_version >= 3 embeds the
#    post-pre-pass LLBC inside the cert itself, so the separate
#    -emit-llbc-json stub is no longer needed).
echo "[2/6] aeneas -emit-cert ..."
"$AENEAS" -emit-cert "$TESTS/llbc/incr_cert.llbc"

# 3. Lean checker: parse + typecheck + replay + emit
echo "[3/6] lake build && aeneas-check ..."
( cd "$CHECKER" && lake build aeneas-check )
"$CHECKER/.lake/build/bin/aeneas-check" \
    "$TESTS/llbc/incr_cert.cert.json" \
    --out "$CHECKER/tests/Generated/Incr.lean" \
    --rust-model "$DIFF/src/model.rs"

# 4. Lean smoke tests (checker logic)
echo "[4/6] lean checker tests ..."
( cd "$CHECKER" && lake env lean --run tests/Direct/Replay.lean )
( cd "$CHECKER" && lake env lean --run tests/Direct/Emit.lean )

# 5. Compile the generated Lean against the RuntimeShim. This is the
#    "does the emitter actually produce well-typed Lean?" test. The
#    shim is a minimal Aeneas.Std stand-in (see lakefile.lean).
echo "[5/6] compile generated Lean against RuntimeShim ..."
( cd "$CHECKER" && lake build GeneratedTests )

# 6. Differential cargo test
echo "[6/6] cargo test ..."
( cd "$DIFF" && cargo test --release )

echo
echo "✓ vertical slice (M2-M8) ok"
