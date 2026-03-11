#!/usr/bin/env bash
# Wrapper for lake build that outputs to /tmp/lake-build.log
# Usage: ./scripts/lake-build.sh <target>
cd "$(dirname "$0")/.."
# Find lake: prefer elan-managed lake, fall back to PATH
LAKE="${LAKE:-$(command -v lake 2>/dev/null)}"
if [ -z "$LAKE" ]; then
  for candidate in \
      "$HOME/.elan/bin/lake" \
      "/root/.elan/bin/lake" \
      "/Users/kalmanlajko/.elan/bin/lake"; do
    if [ -x "$candidate" ]; then
      LAKE="$candidate"
      break
    fi
  done
fi
if [ -z "$LAKE" ]; then
  echo "ERROR: lake not found. Install elan: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash" >&2
  exit 1
fi
"$LAKE" build --old -j "$(nproc)" "$@" > /tmp/lake-build.log 2>&1
exit $?
