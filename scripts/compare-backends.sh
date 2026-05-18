#!/usr/bin/env bash
# Side-by-side comparison of `aeneas -backend lean` (standard / L₀)
# and `aeneas-check` (new cert pipeline / L₁) output for a Rust input.
#
# Two modes:
#
#   scripts/compare-backends.sh <tests/src/foo.rs>
#     Interactive single-fixture diff: emits L₀ to /tmp/aeneas_compare/
#     and L₁ to /tmp/aeneas_compare/, prints both with a unified diff.
#
#   scripts/compare-backends.sh --sweep [--regen-divergent]
#     Session-6 Item 2: G_byte gate. Walks every tests/llbc/*.llbc
#     and emits L₀ via mainline `aeneas -backend lean -dest /tmp/...`
#     vs L₁ via `aeneas-check --out /tmp/...`. Classifies each fixture
#     as pass / divergent / mismatch / skip:
#       pass      — L₀ and L₁ are byte-identical.
#       divergent — L₀ ≠ L₁ AND the fixture is listed in
#                   scripts/compare-backends-known-divergent.txt with
#                   a one-sentence reason (whitespace, banner, etc.).
#       mismatch  — L₀ ≠ L₁ AND the fixture is *not* in the
#                   known-divergent list (surfaces as a real fail).
#       skip      — L₀ or L₁ emit failed upstream (we can't compare).
#     Prints a Markdown table summary. Exits non-zero iff any fixture
#     is `mismatch`. `--regen-divergent` overwrites the known-divergent
#     file with every currently-divergent fixture's name and a
#     placeholder reason (to be hand-edited).

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# Resolve aeneas binary. Prefer the locally-built dune binary inside
# the worktree (which carries the Session-5+ cert-format changes);
# fall back to a sibling `bin/aeneas` shim when present.
AENEAS=""
if [[ -x "$ROOT/src/_build/default/main.exe" ]]; then
    AENEAS="$ROOT/src/_build/default/main.exe"
elif [[ -x "$ROOT/bin/aeneas" ]]; then
    AENEAS="$ROOT/bin/aeneas"
else
    echo "[error] no aeneas binary found at $ROOT/src/_build/default/main.exe or $ROOT/bin/aeneas" >&2
    exit 1
fi
CHECKER="$ROOT/aeneas-lean-checker/.lake/build/bin/aeneas-check"
KNOWN_DIVERGENT="$ROOT/scripts/compare-backends-known-divergent.txt"

# ---------------------------------------------------------------------
# Sweep mode
# ---------------------------------------------------------------------
if [[ "${1-}" == "--sweep" ]] || [[ "${1-}" == "--regen-divergent" ]]; then
    REGEN_DIVERGENT=0
    [[ "${1-}" == "--regen-divergent" ]] && REGEN_DIVERGENT=1
    [[ "${2-}" == "--regen-divergent" ]] && REGEN_DIVERGENT=1

    # Sanity-check binaries.
    [[ -x "$CHECKER" ]] || {
        echo "[error] aeneas-check binary not built; run \`cd aeneas-lean-checker && lake build aeneas-check\`" >&2
        exit 1
    }

    OUT_DIR="/tmp/aeneas-g-byte-sweep"
    rm -rf "$OUT_DIR"
    mkdir -p "$OUT_DIR"

    # Known-divergent entries: lines of `<fixture>: <reason>`. We keep
    # the file path in a variable and grep against it per fixture
    # (avoids macOS bash-3.2's lack of associative arrays).
    lookup_reason() {
        local fx="$1"
        [[ -f "$KNOWN_DIVERGENT" ]] || { echo ""; return; }
        local line
        line=$(grep -E "^[[:space:]]*${fx}[[:space:]]*:" "$KNOWN_DIVERGENT" 2>/dev/null | head -1) || true
        if [[ -n "$line" ]]; then
            local r="${line#*:}"
            # Trim leading whitespace.
            echo "${r#"${r%%[![:space:]]*}"}"
        else
            echo ""
        fi
    }

    # Collect newly-divergent fixtures when regenerating the list.
    regen_divergent_lines=()

    # Counters per status.
    pass_count=0
    divergent_count=0
    mismatch_count=0
    skip_count=0

    # Tabular rows for the Markdown summary.
    rows=()
    rows+=("Fixture | Status | Bytes L₀ | Bytes L₁ | Notes")
    rows+=("--- | --- | --- | --- | ---")

    # Iterate fixtures.
    for llbc in "$ROOT"/tests/llbc/*.llbc; do
        base=$(basename "$llbc" .llbc)
        cert="$ROOT/tests/llbc/${base}.cert.json"
        l0_dir="$OUT_DIR/${base}-l0"
        l1_file="$OUT_DIR/${base}-l1.lean"
        mkdir -p "$l0_dir"

        l0_status="pending"
        l1_status="pending"

        # L₀: mainline aeneas.
        if "$AENEAS" -backend lean -dest "$l0_dir" "$llbc" >/dev/null 2>"$OUT_DIR/${base}-l0.err"; then
            l0_status="ok"
        else
            l0_status="fail"
        fi

        # L₁: aeneas-check (new cert pipeline).
        if [[ -f "$cert" ]]; then
            if "$CHECKER" "$cert" --out "$l1_file" >/dev/null 2>"$OUT_DIR/${base}-l1.err"; then
                l1_status="ok"
            else
                l1_status="fail"
            fi
        else
            l1_status="no-cert"
        fi

        # Find the L₀ output file (mainline writes one .lean per crate).
        l0_file=$(find "$l0_dir" -maxdepth 2 -name '*.lean' 2>/dev/null | head -1)

        # Classify.
        if [[ "$l0_status" != "ok" || "$l1_status" != "ok" ]]; then
            skip_count=$((skip_count + 1))
            reason_l0="$l0_status"
            reason_l1="$l1_status"
            rows+=("$base | skip | $reason_l0 | $reason_l1 | (emit failed)")
            continue
        fi

        if [[ ! -f "$l0_file" ]]; then
            skip_count=$((skip_count + 1))
            rows+=("$base | skip | no-file | ok | (no L₀ .lean produced)")
            continue
        fi

        l0_bytes=$(wc -c < "$l0_file" | tr -d ' ')
        l1_bytes=$(wc -c < "$l1_file" | tr -d ' ')

        if cmp -s "$l0_file" "$l1_file"; then
            pass_count=$((pass_count + 1))
            rows+=("$base | pass | $l0_bytes | $l1_bytes | byte-identical")
        else
            reason=$(lookup_reason "$base")
            if [[ -n "$reason" ]]; then
                divergent_count=$((divergent_count + 1))
                rows+=("$base | divergent | $l0_bytes | $l1_bytes | $reason")
            else
                mismatch_count=$((mismatch_count + 1))
                rows+=("$base | mismatch | $l0_bytes | $l1_bytes | (new — not in known-divergent.txt)")
                regen_divergent_lines+=("$base: PLACEHOLDER reason — please document")
            fi
        fi
    done

    # --- Print summary table ---
    echo
    echo "## G_byte sweep summary"
    echo
    printf '%s\n' "${rows[@]}"
    echo
    total=$((pass_count + divergent_count + mismatch_count + skip_count))
    echo "Totals: pass=$pass_count  divergent=$divergent_count  mismatch=$mismatch_count  skip=$skip_count  (total=$total)"

    # Regenerate known-divergent file with placeholders if requested.
    if [[ $REGEN_DIVERGENT -eq 1 ]]; then
        # Keep any existing entries from the current file, then append
        # new placeholders for mismatches not already covered.
        existing_lines=()
        if [[ -f "$KNOWN_DIVERGENT" ]]; then
            while IFS= read -r line || [[ -n "$line" ]]; do
                # Skip the header comment block on rewrite (we regen it).
                [[ -z "$line" || "$line" =~ ^[[:space:]]*# ]] && continue
                existing_lines+=("$line")
            done < "$KNOWN_DIVERGENT"
        fi
        {
            echo "# G_byte gate: fixtures whose L₀ (mainline) and L₁ (aeneas-check)"
            echo "# outputs differ in ways that are *known* and *harmless*. One line"
            echo "# per fixture: <fixture>: <one-sentence reason>. Lines starting"
            echo "# with '#' are comments. Blank lines are ignored."
            echo "#"
            echo "# Regenerate via \`scripts/compare-backends.sh --regen-divergent\`,"
            echo "# then hand-edit each PLACEHOLDER to describe the divergence (or"
            echo "# fix it). When a divergence is fixed, remove the line."
            echo
            if [[ ${#existing_lines[@]} -gt 0 ]]; then
                printf '%s\n' "${existing_lines[@]}" | sort -u
            fi
            if [[ ${#regen_divergent_lines[@]} -gt 0 ]]; then
                printf '%s\n' "${regen_divergent_lines[@]}" | sort -u
            fi
        } > "$KNOWN_DIVERGENT"
        echo
        echo "[info] regenerated $KNOWN_DIVERGENT with ${#regen_divergent_lines[@]} new placeholder(s)."
    fi

    if [[ $mismatch_count -gt 0 ]]; then
        echo
        echo "[fail] $mismatch_count unlisted mismatch(es). Either fix the"
        echo "       divergence or add the fixture to $KNOWN_DIVERGENT"
        echo "       with a documented reason (or use --regen-divergent)."
        exit 1
    fi
    exit 0
fi

# ---------------------------------------------------------------------
# Interactive single-fixture mode (original behaviour, preserved).
# ---------------------------------------------------------------------
SRC="${1:?usage: $0 <tests/src/foo.rs> | --sweep [--regen-divergent]}"

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

if [[ ! -f "$LLBC" ]]; then
    echo "==> charon rustc"
    "$CHARON" rustc --preset=aeneas --dest-file="$LLBC" -- "$SRC" --crate-type=lib
fi

echo "==> aeneas -emit-cert (new pipeline)"
"$AENEAS" -emit-cert "$LLBC" >/dev/null

echo "==> aeneas -backend lean (standard pipeline)"
"$AENEAS" -backend lean -dest "$STD_OUT" "$LLBC" 2>&1 | grep -E "(Generated|Error)" || true

echo "==> aeneas-check --out (new pipeline)"
"$CHECKER" "$ROOT/tests/llbc/${base}.cert.json" \
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
