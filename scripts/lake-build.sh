#!/usr/bin/env bash
# Wrapper for lake build that outputs to /tmp/lake-build.log
# Usage: ./scripts/lake-build.sh <target>
cd "$(dirname "$0")/.."
/Users/kalmanlajko/.elan/bin/lake build "$@" > /tmp/lake-build.log 2>&1
exit $?
