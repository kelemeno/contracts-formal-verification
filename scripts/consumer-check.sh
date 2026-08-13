#!/usr/bin/env bash
# Build the GENERATED module that consumes each given spec.
#
# A spec file can build perfectly while breaking the generated file that uses it, because
# the generated module references lemmas the spec is expected to provide but the spec's
# own module never needs.  Editing a spec by splicing over a region is how you lose one:
#
#     lemma <loop>_cond_abs_of_code   -- required by generated/<loop>.lean, referenced
#                                     -- nowhere in <loop>_user.lean itself
#
# Four converted loops lost exactly that lemma in one session.  Every per-module build
# stayed green, spec-binds-check stayed green, and the breakage only surfaced when
# something upstream (fun_updateLeaf) tried to build.
#
# So: after editing a spec, build its consumer.  `specs/X_user.lean` is consumed by
# `generated/X.lean` (the same path without the `_user` suffix).
#
# Usage: scripts/consumer-check.sh <spec_user.lean> [...]
#        scripts/consumer-check.sh --changed        # everything unpushed
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [ "${1:-}" = "--changed" ]; then
  FILES=$(git diff --name-only origin/main..HEAD -- specs/ | grep '_user\.lean$')
else
  FILES="$*"
fi
[ -n "$FILES" ] || { echo "usage: $0 <spec_user.lean> [...] | --changed"; exit 2; }

fail=0
total=0
for f in $FILES; do
  [ -f "$f" ] || { echo "SKIP  $f (missing)"; continue; }
  # A hand-written support module (specs/StateOk.lean) has no generated counterpart, so
  # there is nothing to consume.  Without this it reports FAIL "no such file", which is a
  # false red -- and a checker that cries wolf is worse than no checker.
  gen="generated/$(echo "$f" | sed 's|^specs/||; s|_user\.lean$|.lean|')"
  [ -f "$gen" ] || { echo "SKIP  $f (no generated consumer)"; continue; }
  total=$((total + 1))
  mod="generated.$(echo "$f" | sed 's|^specs/||; s|/|.|g; s|_user\.lean$||')"
  # </dev/null: lake reads stdin and will eat the rest of a piped file list
  if ~/.elan/bin/lake build --old "$mod" < /dev/null > /tmp/consumer_$$.log 2>&1; then
    echo "ok    $mod"
  else
    echo "FAIL  $mod"
    grep -E "^error" /tmp/consumer_$$.log | grep -v "linter\|note:" | head -3
    fail=$((fail + 1))
  fi
  rm -f /tmp/consumer_$$.log
done

echo
if [ "$fail" -gt 0 ]; then
  echo "$fail of $total consumer(s) FAILED -- the spec builds but its generated user does not"
  exit 1
fi
echo "$total consumer(s) ok"
