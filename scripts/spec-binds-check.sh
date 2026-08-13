#!/usr/bin/env bash
# Does a spec's abs_of_concrete proof actually BIND to the spec, or would it close anything?
#
# Found the hard way (2026-08-13): the probe shape
#     def A_x ... := s₉ = s₀
#     lemma x_abs_of_concrete ... := by unfold ...; apply spec_eq; intro _hne hc; exact hc
# BUILDS against concrete specs with real content. A file left that way is a trivial spec that
# passes every other check here -- clean build, no sorry, no sorryAx, classified REAL.
#
# The test: append `∧ False` to the spec's definition. If the module still builds, the proof is
# not binding to what the definition says, and the spec is worthless.
#
# Audited 2026-08-13: all 19 specs closed that day BIND, and a 10-spec sample spread across
# the pre-existing corpus (324 non-alias, non-sorry specs) binds too -- 9 ok, 1 skipped for
# using a hand-written naming convention rather than A_<name>. So ghost specs are NOT endemic;
# the probe shape is the way they get created, and it was only ever used interactively.
#
# LOOPS are covered too: for a `for_<id>_user.lean` the checker weakens AFor_<id>, the loop's
# postcondition, since every closure lemma is stated in terms of it. All 25 REAL loops bind
# (audited 2026-08-13). A loop whose AFor does not bind would be the TRUE-FOR problem wearing
# a disguise -- green, sorry-free, and classified REAL by the content audit.
#
# Usage: scripts/spec-binds-check.sh <path-to-_user.lean> [...]
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fail=0
for f in "$@"; do
  [ -f "$f" ] || { echo "SKIP  $f (missing)"; continue; }
  mod=$(echo "$f" | sed 's|^specs/|specs.|; s|/|.|g; s|\.lean$||')
  name=$(basename "$f" _user.lean)
  cp "$f" "/tmp/binds_$$.bak"
  # weaken the spec: turn `def A_… : Prop := BODY` into `… := (BODY) ∧ False`
  python3 - "$f" "$name" <<'PY'
import sys, re
p, n = sys.argv[1], sys.argv[2]
s = open(p).read()
# function/block/if/switch specs are `def A_<name>`; LOOP specs are `def AFor_<name>` -- weaken
# the loop's POSTCONDITION, since every closure lemma is stated in terms of it.
for pat in (r'^def A_?' + re.escape(n) + r'\b', r'^def AFor_' + re.escape(n) + r'\b'):
    m = re.search(r'(' + pat + r'[^\n]*?:=[ \n])(.*?)(?=\n\s*\n|\nlemma|\ntheorem|\nend)', s, re.S | re.M)
    if m:
        open(p, 'w').write(s[:m.start(2)] + '(' + m.group(2) + ') ∧ False' + s[m.end(2):])
        sys.exit(0)
sys.exit(3)
PY
  case $? in
    3) echo "SKIP  $name (could not locate its def)"; cp "/tmp/binds_$$.bak" "$f"; continue;;
  esac
  if ~/.elan/bin/lake build --old "$mod" >/dev/null 2>&1; then
    echo "!! UNBOUND  $name -- builds with a FALSE spec; the proof closes anything"
    fail=1
  else
    echo "ok    $name"
  fi
  cp "/tmp/binds_$$.bak" "$f"
done
rm -f "/tmp/binds_$$.bak"
~/.elan/bin/lake build --old $(for f in "$@"; do echo "$f" | sed 's|^specs/|specs.|; s|/|.|g; s|\.lean$||'; done) >/dev/null 2>&1
exit "$fail"
