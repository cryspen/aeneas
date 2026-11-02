#!/usr/bin/env bash
# Checks that every fork commit belongs to one of the patches documented in
# `fork/patches/`, which the rebase of the fork onto upstream relies on.
#
# Usage:
#   ci-check-fork-patches.sh REV...
#       Check the commits selected by `git rev-list --no-merges REV...`, e.g.
#       `BASE..HEAD --not upstream/main` for the commits of a pull request
#       that do not come from upstream. Run it in a checkout of the head of
#       these commits: patches are looked up in its `fork/patches/`.
#
# Each commit must:
# - carry exactly one `Fork-Patch: <name>` trailer;
# - name a patch documented in `fork/patches/<name>.md` at `HEAD` (a patch
#   may be documented by its last commit only);
# - modify the files of its patch: `fork/patches/<name>.md` or a
#   `fork/scripts/<name>.*` script.
set -euo pipefail

if [ $# -eq 0 ]; then
    sed -n '/^# Usage:/,/^#$/p' "$0" | sed '$d; s/^# \{0,1\}//' >&2
    exit 1
fi

errors=0
error() {
    echo "error: $(git log -1 --format='%h "%s"' "$commit"): $1" >&2
    errors=$((errors + 1))
}

commits=$(git rev-list --no-merges "$@")
for commit in $commits; do
    patches=$(git log -1 --format='%(trailers:key=Fork-Patch,valueonly)' "$commit" | sed '/^$/d')
    if [ -z "$patches" ]; then
        error "missing a \`Fork-Patch: <name>\` trailer"
        continue
    fi
    if [ "$(echo "$patches" | wc -l)" -ne 1 ]; then
        error "more than one \`Fork-Patch\` trailer: $(echo $patches)"
        continue
    fi
    patch="$patches"
    doc="fork/patches/$patch.md"
    if ! git cat-file -e "HEAD:$doc" 2>/dev/null; then
        error "unknown patch \`$patch\`: no $doc"
        continue
    fi
    if ! git diff-tree --no-commit-id --name-only -r "$commit" -- "$doc" "fork/scripts/$patch.*" | grep -q .; then
        error "does not modify $doc (nor a fork/scripts/$patch.* script)"
    fi
done

count=$(echo "$commits" | sed '/^$/d' | wc -l)
if [ "$errors" -ne 0 ]; then
    echo "$errors error(s) in $count commit(s); see fork/patches/ for the documented patches." >&2
    exit 1
fi
echo "All $count commit(s) belong to a documented fork patch."
