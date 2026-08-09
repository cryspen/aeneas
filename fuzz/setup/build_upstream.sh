#!/usr/bin/env bash
# fuzz/setup/build_upstream.sh — clone/build the UPSTREAM target
# (AeneasVerif/aeneas, tracking main by default; charon pin 527ea8e3 = v0.1.225)
# and export the env-var contract.
#
# Idempotent: re-uses an existing checkout at $AENEAS_UPSTREAM_ROOT. Can be
# executed or sourced (see build_fork.sh header for the sourcing contract).
#
# Requires: git, opam switch `aeneas`, rustup + cargo (upstream charon shells
# out to its nightly toolchain at build AND run time). Downloads are OK.
#
# NOTE: upstream vendors charon-ml in-tree via a `src/charon` symlink, so
# building aeneas builds charon-ml too; we build the charon *binary* separately
# (its own Makefile) since the fuzz pipeline needs the wrapper at runtime.

set -uo pipefail

_SOURCED=0
(return 0 2>/dev/null) && _SOURCED=1

_dir="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
# shellcheck source=common.sh
. "$_dir/common.sh"

build_upstream() {
  # A fixed pin (if given) overrides the default `main` tracking.
  local ref="${AENEAS_UPSTREAM_PIN:-$AENEAS_UPSTREAM_REF}"
  log "upstream: root=$AENEAS_UPSTREAM_ROOT ref=$ref"

  need_cmd git   "install git" || return 1
  need_cmd opam  "install opam and create the '$OPAM_SWITCH' switch" || return 1
  need_cmd rustup "install rustup (upstream charon needs it at build+run time)" || return 1
  need_cmd cargo  "install cargo (via rustup)" || return 1
  if ! have_opam_switch "$OPAM_SWITCH"; then
    err "opam switch '$OPAM_SWITCH' is missing (see build_fork.sh for creation steps)."
    return 1
  fi

  # --- clone / update aeneas ---
  if [ ! -d "$AENEAS_UPSTREAM_ROOT/.git" ]; then
    log "cloning AeneasVerif/aeneas -> $AENEAS_UPSTREAM_ROOT"
    git clone https://github.com/AeneasVerif/aeneas "$AENEAS_UPSTREAM_ROOT" \
      || { err "git clone failed"; return 1; }
  fi
  ( cd "$AENEAS_UPSTREAM_ROOT" \
      && git fetch --all --tags --quiet \
      && git checkout "$ref" \
      && { [ -n "${AENEAS_UPSTREAM_PIN:-}" ] || git pull --ff-only --quiet 2>/dev/null || true; } ) \
    || { err "git checkout '$ref' failed in $AENEAS_UPSTREAM_ROOT"; return 1; }
  log "upstream aeneas at $(cd "$AENEAS_UPSTREAM_ROOT" && git rev-parse --short HEAD)"

  eval "$(opam env --switch="$OPAM_SWITCH")" || { err "opam env failed"; return 1; }

  # --- upstream charon ---
  # Prefer the pin recorded in the checkout's own charon-pin (last line);
  # fall back to the documented $CHARON_UPSTREAM_PIN.
  local charon_pin="$CHARON_UPSTREAM_PIN"
  if [ -f "$AENEAS_UPSTREAM_ROOT/charon-pin" ]; then
    charon_pin="$(tail -1 "$AENEAS_UPSTREAM_ROOT/charon-pin" | tr -d '[:space:]')"
    [ -n "$charon_pin" ] || charon_pin="$CHARON_UPSTREAM_PIN"
  fi
  if [ -x "$CHARON_UPSTREAM_BIN" ]; then
    log "upstream charon present: $CHARON_UPSTREAM_BIN"
  else
    log "building upstream charon at pin $charon_pin"
    if [ ! -d "$AENEAS_UPSTREAM_ROOT/charon/.git" ]; then
      git clone https://github.com/AeneasVerif/charon "$AENEAS_UPSTREAM_ROOT/charon" \
        || { err "charon clone failed"; return 1; }
    fi
    ( cd "$AENEAS_UPSTREAM_ROOT/charon" \
        && git fetch --all --quiet \
        && git checkout "$charon_pin" \
        && make build ) \
      || { err "upstream charon build failed (pin $charon_pin)"; return 1; }
  fi
  if [ ! -x "$CHARON_UPSTREAM_BIN" ]; then
    warn "upstream charon binary not found at $CHARON_UPSTREAM_BIN after build; check 'make build' output"
  fi

  # --- upstream aeneas binary ---
  log "building upstream aeneas (dune build) ..."
  ( cd "$AENEAS_UPSTREAM_ROOT/src" && dune build ) \
    || { err "dune build failed in $AENEAS_UPSTREAM_ROOT/src (is src/charon -> charon-ml resolvable?)"; return 1; }
  mkdir -p "$AENEAS_UPSTREAM_ROOT/bin"
  cp -f "$AENEAS_UPSTREAM_ROOT/src/_build/default/main.exe" "$AENEAS_UPSTREAM_ROOT/bin/aeneas" \
    || { err "failed to copy upstream main.exe -> bin/aeneas"; return 1; }
  log "upstream aeneas -> $AENEAS_UPSTREAM_ROOT/bin/aeneas"

  export_var AENEAS_UPSTREAM_ROOT "$AENEAS_UPSTREAM_ROOT"
  export_var CHARON_UPSTREAM_BIN  "$CHARON_UPSTREAM_BIN"
  # NOTE: the upstream target's TOML prepends "$CHARON_UPSTREAM dir:${PATH}"
  # itself (extra_env), so we do NOT clobber PATH here — but rustup/cargo MUST be
  # on the harness process's PATH at run time (charon shells out to them).
  log "upstream ready. (reminder: keep rustup/cargo on PATH when running the harness)"
  return 0
}

build_upstream
_rc=$?
print_env
if [ "$_SOURCED" = 1 ]; then
  return $_rc
else
  exit $_rc
fi
