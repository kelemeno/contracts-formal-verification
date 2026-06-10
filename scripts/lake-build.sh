#!/usr/bin/env bash
# Wrapper for lake build that outputs to /tmp/lake-build.log
# Usage: ./scripts/lake-build.sh <target>
cd "$(dirname "$0")/.."

# Resolve `lake` from PATH, falling back to the standard elan install location.
LAKE="$(command -v lake || true)"
if [ -z "$LAKE" ]; then
    for cand in "$HOME/.elan/bin/lake" /usr/local/bin/lake; do
        [ -x "$cand" ] && LAKE="$cand" && break
    done
fi
if [ -z "$LAKE" ]; then
    echo "Error: 'lake' not found. Install elan (https://github.com/leanprover/elan) or add it to PATH." >&2
    exit 1
fi

"$LAKE" build --old "$@" > /tmp/lake-build.log 2>&1
exit $?
