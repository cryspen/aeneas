#!/usr/bin/env bash
# Rewires a checkout of hax (https://github.com/cryspen/hax) to use a local
# aeneas, so that hax's Lean examples and Lean proof library can be checked
# against an aeneas commit before hax pins it.
#
# Usage:
#   ci-hax-main.sh list-examples HAX_DIR
#       Print, one per line, the hax examples that have a Lean target.
#   ci-hax-main.sh setup HAX_DIR AENEAS_DIR AENEAS_BIN_DIR [EXAMPLE...]
#       Point hax at the aeneas and charon binaries in AENEAS_BIN_DIR (e.g. the
#       `bin` directory of `nix build .#aeneas`, which also contains the charon
#       aeneas is built against) and at the Lean library in
#       AENEAS_DIR/backends/lean. The Lean proof library is always rewired;
#       the examples only when listed. Needs `lake` on PATH.
set -euo pipefail

usage() {
    sed -n '/^# Usage:/,/^set /p' "$0" | sed '$d; s/^# \{0,1\}//' >&2
    exit 1
}

# The examples whose Makefile has a `lean` target.
list_examples() {
    local hax="$1" makefile
    for makefile in "$hax"/examples/*/Makefile; do
        if grep -q '^lean:' "$makefile"; then
            basename "$(dirname "$makefile")"
        fi
    done
}

# Replace the git source of the `aeneas` requirement in a `lakefile.toml` with
# a path source.
require_aeneas_by_path() {
    local lakefile="$1" path="$2"
    # Expects the `git = …` line of the requirement to be followed by its
    # `rev = …` line.
    sed -i "/^git = .*aeneas/{s|.*|path = \"$path\"|;n;/^rev = /d}" "$lakefile"
    if ! grep -qx "path = \"$path\"" "$lakefile" || grep -q '^rev = ' "$lakefile"; then
        echo "error: could not rewrite the aeneas requirement in $lakefile" >&2
        exit 1
    fi
}

# Write the Lean toolchain into a `lean-toolchain` file, unless it already
# names it.
set_lean_toolchain() {
    if [ "$(tr -d '[:space:]' < "$1")" != "$2" ]; then
        echo "$2" > "$1"
    fi
}

# Append the tool and version pins to the `hax.toml` of the examples' Cargo
# workspace, creating it if needed. hax applies workspace pins to every
# example that does not pin the tools itself.
pin_tools() {
    local hax_toml="$1" aeneas_exe="$2" charon_exe="$3" lean_toolchain="$4"
    if [ -f "$hax_toml" ] && grep -Eq '^\[(tools|versions)\]' "$hax_toml"; then
        echo "error: $hax_toml already has a [tools] or [versions] table" >&2
        exit 1
    fi
    cat >> "$hax_toml" <<EOF

[tools]
aeneas = { path = "$aeneas_exe" }
charon = { path = "$charon_exe" }

[versions]
lean = "$lean_toolchain"
EOF
}

setup() {
    [ $# -ge 3 ] || usage
    local hax aeneas bin
    hax="$(realpath "$1")"
    aeneas="$(realpath "$2")"
    bin="$(realpath "$3")"
    shift 3

    # hax expects `charon-driver` next to `charon`, which only holds in
    # charon's own package, so resolve the symlinks.
    local aeneas_exe charon_exe
    aeneas_exe="$(realpath "$bin/aeneas")"
    charon_exe="$(realpath "$bin/charon")"
    local exe
    for exe in "$aeneas_exe" "$charon_exe" "$(dirname "$charon_exe")/charon-driver"; do
        [ -x "$exe" ] || { echo "error: $exe is not an executable" >&2; exit 1; }
    done
    local lean_toolchain
    lean_toolchain="$(tr -d '[:space:]' < "$aeneas/backends/lean/lean-toolchain")"

    echo "Rewiring hax at $hax ($(git -C "$hax" rev-parse HEAD))"
    echo "  aeneas Lean library: $aeneas/backends/lean"
    echo "  aeneas:              $aeneas_exe"
    echo "  charon:              $charon_exe"
    echo "  Lean toolchain:      $lean_toolchain"

    # The Lean proof library, which every example depends on by path.
    local proof_libs="$hax/hax-lib/proof-libs/lean"
    require_aeneas_by_path "$proof_libs/lakefile.toml" "$aeneas/backends/lean"
    set_lean_toolchain "$proof_libs/lean-toolchain" "$lean_toolchain"
    (cd "$proof_libs" && lake update)

    [ $# -eq 0 ] && return
    pin_tools "$hax/examples/hax.toml" "$aeneas_exe" "$charon_exe" "$lean_toolchain"
    local example dir lean_dir
    for example in "$@"; do
        dir="$hax/examples/$example"
        grep -q '^lean:' "$dir/Makefile" || { echo "error: $example has no Lean target" >&2; exit 1; }
        if grep -Eq '^\[(tools|versions)\]' "$dir/hax.toml"; then
            echo "error: $dir/hax.toml pins tools itself, overriding the workspace pins" >&2
            exit 1
        fi
        # The Lean package of each scenario; `cargo hax extract` generates
        # it if it is not committed.
        for lean_dir in "$dir"/proofs/*/lean; do
            [ -f "$lean_dir/lakefile.toml" ] || continue
            set_lean_toolchain "$lean_dir/lean-toolchain" "$lean_toolchain"
            (cd "$lean_dir" && lake update)
        done
    done
}

[ $# -ge 1 ] || usage
command="$1"
shift
case "$command" in
    list-examples) [ $# -eq 1 ] || usage; list_examples "$1" ;;
    setup) setup "$@" ;;
    *) usage ;;
esac
