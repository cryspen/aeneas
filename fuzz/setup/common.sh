#!/usr/bin/env bash
# fuzz/setup/common.sh — shared helpers + pinned toolchain facts for the Aeneas
# fuzzing harness setup scripts. Safe to source repeatedly; sets (but does NOT
# build) the env-var contract that the target TOMLs consume via `${VAR:-default}`
# substitution (see fuzz/targets/*.toml and fuzz/harness/src/config.rs).
#
# ---------------------------------------------------------------------------
# Env-var contract (each is overridable; the value shown is the default). These
# names match the `${VAR}` references in the target TOMLs.
#
#   AENEAS_FORK_ROOT      fork checkout root (holds bin/aeneas, backends/lean)
#   CHARON_FORK_ROOT      fork charon checkout (default: $AENEAS_FORK_ROOT/charon)
#   CHARON_FORK_BIN       fork charon wrapper (v0.1.196)
#   AENEAS_UPSTREAM_ROOT  upstream aeneas checkout        (default /tmp/aeneas-upstream)
#   CHARON_UPSTREAM_BIN   upstream charon wrapper (v0.1.225)
#   AENEAS_UPSTREAM_PIN   upstream aeneas commit/branch to build (unset => track
#                         `main`; recorded good commit is $AENEAS_UPSTREAM_GOOD_PIN)
#
# Pinned facts (do not hardcode elsewhere):
#   OPAM_SWITCH=aeneas
#   fork charon        v0.1.196
#   upstream charon    527ea8e3  (= v0.1.225)
#   upstream aeneas    3a8586fa  (recorded good; default build tracks main)
# ---------------------------------------------------------------------------

# Resolve this file's directory portably (works when sourced or executed).
_common_dir="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"

# --- pinned facts ---
: "${OPAM_SWITCH:=aeneas}"
: "${CHARON_FORK_VERSION:=v0.1.196}"
: "${CHARON_UPSTREAM_PIN:=527ea8e3}"          # = v0.1.225
: "${AENEAS_UPSTREAM_GOOD_PIN:=3a8586fa}"     # recorded-good upstream commit
# Upstream tracks latest main by default; set AENEAS_UPSTREAM_PIN to override
# with a fixed commit/tag (e.g. AENEAS_UPSTREAM_PIN=$AENEAS_UPSTREAM_GOOD_PIN).
: "${AENEAS_UPSTREAM_REF:=main}"

# --- path contract (with dev-machine-compatible defaults) ---
# setup/ lives at fuzz/setup, so ../.. is the repo (fork) root.
: "${AENEAS_FORK_ROOT:=$(cd "$_common_dir/../.." && pwd)}"
: "${CHARON_FORK_ROOT:=$AENEAS_FORK_ROOT/charon}"
: "${CHARON_FORK_BIN:=$CHARON_FORK_ROOT/charon/target/release/charon}"
: "${AENEAS_UPSTREAM_ROOT:=/tmp/aeneas-upstream}"
: "${CHARON_UPSTREAM_BIN:=$AENEAS_UPSTREAM_ROOT/charon/bin/charon}"

# --- logging (all to stderr; no control flow) ---
log()  { echo "[setup] $*" >&2; }
warn() { echo "[setup] warning: $*" >&2; }
err()  { echo "[setup] ERROR: $*" >&2; }

# need_cmd NAME [HINT]  -> 0 if present, else prints an error+hint and returns 1.
need_cmd() {
  if command -v "$1" >/dev/null 2>&1; then
    return 0
  fi
  err "required command '$1' not found on PATH."
  [ -n "${2:-}" ] && echo "        hint: $2" >&2
  return 1
}

# have_opam_switch NAME -> 0 if the opam switch exists.
have_opam_switch() {
  opam switch list --short 2>/dev/null | grep -qx "$1"
}

# export_var NAME VALUE — export for this shell AND (in GitHub Actions) persist
# to $GITHUB_ENV so later workflow steps inherit it. Always returns 0.
export_var() {
  export "$1=$2"
  if [ -n "${GITHUB_ENV:-}" ]; then
    echo "$1=$2" >> "$GITHUB_ENV"
  fi
  return 0
}

# print_env — echo the resolved contract (for humans / CI logs).
print_env() {
  cat >&2 <<EOF
[setup] resolved env-var contract:
          OPAM_SWITCH          = $OPAM_SWITCH
          AENEAS_FORK_ROOT     = $AENEAS_FORK_ROOT
          CHARON_FORK_ROOT     = $CHARON_FORK_ROOT
          CHARON_FORK_BIN      = $CHARON_FORK_BIN
          AENEAS_UPSTREAM_ROOT = $AENEAS_UPSTREAM_ROOT
          CHARON_UPSTREAM_BIN  = $CHARON_UPSTREAM_BIN
          AENEAS_UPSTREAM_REF  = ${AENEAS_UPSTREAM_PIN:-$AENEAS_UPSTREAM_REF}
EOF
}

# Export the defaults now so anything sourcing common.sh sees the contract even
# before a build runs. (A subsequent build script re-exports post-build paths.)
export_var AENEAS_FORK_ROOT     "$AENEAS_FORK_ROOT"
export_var CHARON_FORK_ROOT     "$CHARON_FORK_ROOT"
export_var CHARON_FORK_BIN      "$CHARON_FORK_BIN"
export_var AENEAS_UPSTREAM_ROOT "$AENEAS_UPSTREAM_ROOT"
export_var CHARON_UPSTREAM_BIN  "$CHARON_UPSTREAM_BIN"
