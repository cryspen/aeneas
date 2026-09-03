#!/usr/bin/env bash
# fuzz/setup/env.sh — set/export the env-var contract the target TOMLs expect,
# building targets on demand if they are not present yet. MEANT TO BE SOURCED:
#
#     source fuzz/setup/env.sh            # both targets (build fork if missing)
#     FUZZ_TARGET=fork   source fuzz/setup/env.sh
#     FUZZ_TARGET=upstream source fuzz/setup/env.sh
#     FUZZ_TARGET=both   source fuzz/setup/env.sh
#     FUZZ_SETUP_BUILD=0 source fuzz/setup/env.sh   # never build, just set vars
#
# In CI the build_*.sh scripts are normally run as their own steps first, so by
# the time this is sourced the binaries already exist and this just re-affirms
# the vars (and writes them to $GITHUB_ENV).

_dir="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
# shellcheck source=common.sh
. "$_dir/common.sh"

# Which target(s) to ensure. Default: whatever is asked, else both.
: "${FUZZ_TARGET:=both}"
# Whether env.sh may trigger a build when a target is missing (default: yes).
: "${FUZZ_SETUP_BUILD:=1}"

_env_want_fork=0
_env_want_upstream=0
case "$FUZZ_TARGET" in
  fork)     _env_want_fork=1 ;;
  upstream) _env_want_upstream=1 ;;
  both|*)   _env_want_fork=1; _env_want_upstream=1 ;;
esac

# fork
if [ "$_env_want_fork" = 1 ]; then
  if [ -x "$AENEAS_FORK_ROOT/bin/aeneas" ] && [ -x "$CHARON_FORK_BIN" ]; then
    log "fork already built; using existing binaries."
    export_var AENEAS_FORK_ROOT "$AENEAS_FORK_ROOT"
    export_var CHARON_FORK_ROOT "$CHARON_FORK_ROOT"
    export_var CHARON_FORK_BIN  "$CHARON_FORK_BIN"
  elif [ "$FUZZ_SETUP_BUILD" = 1 ]; then
    log "fork not built; sourcing build_fork.sh ..."
    # shellcheck source=build_fork.sh
    . "$_dir/build_fork.sh" || warn "build_fork.sh returned nonzero"
  else
    warn "fork not built and FUZZ_SETUP_BUILD=0; vars set to defaults only."
  fi
fi

# upstream
if [ "$_env_want_upstream" = 1 ]; then
  if [ -x "$AENEAS_UPSTREAM_ROOT/bin/aeneas" ] && [ -x "$CHARON_UPSTREAM_BIN" ]; then
    log "upstream already built; using existing binaries."
    export_var AENEAS_UPSTREAM_ROOT "$AENEAS_UPSTREAM_ROOT"
    export_var CHARON_UPSTREAM_BIN  "$CHARON_UPSTREAM_BIN"
  elif [ "$FUZZ_SETUP_BUILD" = 1 ]; then
    log "upstream not built; sourcing build_upstream.sh ..."
    # shellcheck source=build_upstream.sh
    . "$_dir/build_upstream.sh" || warn "build_upstream.sh returned nonzero"
  else
    warn "upstream not built and FUZZ_SETUP_BUILD=0; vars set to defaults only."
  fi
fi

print_env
