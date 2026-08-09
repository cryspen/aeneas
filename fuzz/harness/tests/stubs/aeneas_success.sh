#!/bin/sh
# Stub aeneas: success. Emits a Lean file into -dest (if given) and exits 0.
dest=""
prev=""
for a in "$@"; do
  if [ "$prev" = "-dest" ]; then dest="$a"; fi
  prev="$a"
done
if [ -n "$dest" ]; then
  mkdir -p "$dest"
  echo "-- stub lean output" > "$dest/Test.lean"
fi
echo "[Info ] Translation succeeded"
exit 0
