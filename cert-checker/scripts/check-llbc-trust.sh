#!/usr/bin/env bash
# Z1 trust-audit gate: every LLBC metadata read in the cert-walker
# must go through `AeneasCheck.Translate.LlbcTrusted`. Run from repo
# root. Exits non-zero on any raw access in Forward/Loops/Driver.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ROOT="$REPO_ROOT/cert-checker/aeneas-lean-checker/AeneasCheck/Translate"
PATTERNS='lf\.signature\b|lf\.localsTypes\b|lf\.localsNames\b|lf\.body\b|lf\.generics\b|lf\.itemMeta\b|cc\.llbcProgram\b'
hits=$(grep -rEn "$PATTERNS" "$ROOT/Forward.lean" "$ROOT/Loops.lean" "$ROOT/Driver.lean" || true)
if [ -n "$hits" ]; then
  echo "[llbc-trust] raw LLBC reads found in cert-walker (must go through LlbcTrusted):" >&2
  echo "$hits" >&2
  exit 1
fi
echo "[llbc-trust] OK — all LLBC reads route through LlbcTrusted"
