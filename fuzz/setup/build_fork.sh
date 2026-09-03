#!/usr/bin/env bash
# fuzz/setup/build_fork.sh — build/locate the FORK target (cryspen/aeneas
# @ dump-pure-ir-minimal, charon v0.1.196) and export the env-var contract.
#
# Idempotent: skips work that is already done. Can be either executed
# (`bash fuzz/setup/build_fork.sh`, exits with a status) or sourced
# (`source fuzz/setup/build_fork.sh`, leaves the env vars in your shell).
#
# Requires: opam switch `aeneas` (OCaml 5.2.1 + dune + aeneas deps). The fork
# charon (v0.1.196) is expected prebuilt at $CHARON_FORK_BIN; if absent we try a
# `cargo build --release` in the charon checkout (needs rustup + the charon
# pinned nightly toolchain).

set -uo pipefail

_SOURCED=0
(return 0 2>/dev/null) && _SOURCED=1

_dir="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
# shellcheck source=common.sh
. "$_dir/common.sh"

build_fork() {
  log "fork: building at AENEAS_FORK_ROOT=$AENEAS_FORK_ROOT"

  need_cmd opam "install opam (https://opam.ocaml.org), then create the '$OPAM_SWITCH' switch" || return 1
  if ! have_opam_switch "$OPAM_SWITCH"; then
    err "opam switch '$OPAM_SWITCH' is missing."
    echo "        create it, e.g.:" >&2
    echo "          opam switch create $OPAM_SWITCH ocaml-base-compiler.5.2.1" >&2
    echo "          eval \$(opam env --switch=$OPAM_SWITCH) && (cd '$AENEAS_FORK_ROOT/src' && opam install --deps-only .)" >&2
    return 1
  fi
  eval "$(opam env --switch="$OPAM_SWITCH")" || { err "opam env failed"; return 1; }

  # --- fork charon (v0.1.196) ---
  if [ -x "$CHARON_FORK_BIN" ]; then
    log "fork charon present: $CHARON_FORK_BIN"
  else
    warn "fork charon not found at $CHARON_FORK_BIN; attempting to build it"
    if [ -d "$CHARON_FORK_ROOT/charon" ]; then
      need_cmd cargo "install rustup and the charon pinned nightly toolchain (see $CHARON_FORK_ROOT/rust-toolchain)" || return 1
      # Pin charon to the commit in the repo's ./charon-pin (authoritative — the
      # flake's check-charon-pin enforces flake.lock matches it), falling back to
      # the configured $CHARON_FORK_VERSION tag.
      _pin="$(tail -1 "$AENEAS_FORK_ROOT/charon-pin" 2>/dev/null || true)"
      if [ -n "${_pin:-}" ]; then
        log "fork charon: checking out pinned commit $_pin (from ./charon-pin)"
        ( cd "$CHARON_FORK_ROOT" && git fetch --all --tags --quiet && git checkout --quiet "$_pin" ) \
          || warn "could not checkout $_pin; building the current checkout"
      else
        warn "no ./charon-pin found; building the current charon checkout ($CHARON_FORK_VERSION)"
      fi
      log "building fork charon (cargo build --release) in $CHARON_FORK_ROOT/charon ..."
      ( cd "$CHARON_FORK_ROOT/charon" && cargo build --release ) || { err "fork charon build failed"; return 1; }
      # The wrapper lives at target/release/charon; charon-driver sits beside it.
    else
      err "no charon checkout at $CHARON_FORK_ROOT (expected the charon-pin / v$CHARON_FORK_VERSION wrapper)."
      echo "        clone AeneasVerif/charon there (git checkout \$(tail -1 charon-pin)) or symlink an existing clone." >&2
      return 1
    fi
  fi
  [ -x "$CHARON_FORK_BIN" ] || { err "fork charon still missing at $CHARON_FORK_BIN"; return 1; }

  # --- fork aeneas (dune build + copy to bin/aeneas) ---
  need_cmd dune "opam install dune (inside the '$OPAM_SWITCH' switch)" || return 1
  log "building fork aeneas (dune build) ..."
  ( cd "$AENEAS_FORK_ROOT/src" && dune build ) || { err "dune build failed in $AENEAS_FORK_ROOT/src"; return 1; }
  mkdir -p "$AENEAS_FORK_ROOT/bin"
  cp -f "$AENEAS_FORK_ROOT/src/_build/default/main.exe" "$AENEAS_FORK_ROOT/bin/aeneas" \
    || { err "failed to copy main.exe -> bin/aeneas"; return 1; }
  log "fork aeneas -> $AENEAS_FORK_ROOT/bin/aeneas"

  export_var AENEAS_FORK_ROOT "$AENEAS_FORK_ROOT"
  export_var CHARON_FORK_ROOT "$CHARON_FORK_ROOT"
  export_var CHARON_FORK_BIN  "$CHARON_FORK_BIN"
  log "fork ready."
  return 0
}

build_fork
_rc=$?
print_env
if [ "$_SOURCED" = 1 ]; then
  return $_rc
else
  exit $_rc
fi
