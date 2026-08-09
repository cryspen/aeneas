#!/bin/sh
# Stub charon: argv is `{output} {input}` (see the test config). Validates the
# input exists (proving rustc-accepted code reached charon) and writes a dummy
# .llbc so the pipeline's charon_ok check passes.
out="$1"
in="$2"
if [ ! -f "$in" ]; then
  echo "charon-stub: missing input $in" >&2
  exit 1
fi
printf 'stub-llbc' > "$out"
exit 0
