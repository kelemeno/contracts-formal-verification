#!/usr/bin/env bash
# Do the lemmas in these spec files ACTUALLY EXIST, and are they axiom-clean?
#
# `lake build <module>` is not proof that a lemma exists.  Lake can REPLAY a stale olean
# and report the module OK while the file on disk does not compile -- that happened twice
# in a row on one file, including on an explicit rebuild, and was only exposed by deleting
# the olean.  What did catch it was a CONSTANT LOOKUP failing.
#
# So this generates one probe module that imports the given specs and `#print axioms` on
# every non-private lemma they declare.  A lemma that does not exist fails the lookup; one
# that rests on an axiom is reported.  Both are things a module build will happily miss.
#
# This is the same reason `#print axioms` rather than `grep -L sorry` is the progress
# metric in this repo: only the constant is authoritative.
#
# AFTER DELETING AN OLEAN, REBUILD BEFORE RUNNING audit-count.sh.  Deleting the stale
# artifact is the right fix when a lookup and a build disagree -- but `audit-count.sh` runs
# `lake env lean` directly, which does NOT rebuild dependencies, so a missing olean makes it
# report dozens of "unknown constant" errors that look exactly like a proof regression and
# are not.  `scripts/consumer-check.sh --changed` puts the artifacts back.
#
# Usage: scripts/constants-check.sh <spec_user.lean> [...]
#        scripts/constants-check.sh --changed        # everything unpushed
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [ "${1:-}" = "--changed" ]; then
  FILES=$(git diff --name-only origin/main..HEAD -- specs/ | grep '\.lean$')
else
  FILES="$*"
fi
[ -n "$FILES" ] || { echo "usage: $0 <spec.lean> [...] | --changed"; exit 2; }

PROBE=specs/ConstantsProbe.lean
trap 'rm -f "$PROBE"' EXIT

python3 - "$PROBE" $FILES <<'PY'
import sys, os, re

probe, files = sys.argv[1], sys.argv[2:]
imports, prints, skipped = [], [], 0

for f in files:
    if not os.path.isfile(f):
        continue
    text = open(f).read()
    mod = f[:-len('.lean')].replace('/', '.')
    # a file's namespace is every `namespace` line, in order
    ns = '.'.join(m.group(1) for m in re.finditer(r'^namespace\s+([\w.]+)', text, re.M))
    names = [m.group(1) for m in
             re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:lemma|theorem)\s+([\w.'?!]+)", text, re.M)]
    # `private` declarations are not addressable from the probe
    priv = set(m.group(1) for m in
               re.finditer(r"^private\s+(?:lemma|theorem)\s+([\w.'?!]+)", text, re.M))
    names = [n for n in names if n not in priv]
    if not names:
        continue
    imports.append(f'import {mod}')
    for n in names:
        prints.append(f'#print axioms {ns + "." if ns else ""}{n}')

open(probe, 'w').write('\n'.join(imports) + '\n\n' + '\n'.join(prints) + '\n')
print(f'probing {len(prints)} constant(s) from {len(imports)} module(s)')
PY

if ~/.elan/bin/lake build --old "specs.ConstantsProbe" < /dev/null > /tmp/constants_$$.log 2>&1; then
  BUILD_OK=1
else
  BUILD_OK=0
fi

python3 - /tmp/constants_$$.log "$BUILD_OK" <<'PY'
import sys, re
log, ok = open(sys.argv[1]).read(), sys.argv[2] == '1'
clean = set(('propext', 'Quot.sound', 'Classical.choice'))
found, dirty = 0, []
for m in re.finditer(r"'([\w.]+)' depends on axioms: \[(.*?)\]", log, re.S):
    ax = [a.strip() for a in m.group(2).replace('\n', ' ').split(',')]
    found += 1
    if not set(ax) <= clean:
        dirty.append((m.group(1), sorted(set(ax) - clean)))
missing = re.findall(r"unknown constant '([\w.]+)'", log)
print(f'  {found} constant(s) verified')
if missing:
    print(f'  {len(missing)} MISSING (the module may have built from a stale olean):')
    for n in sorted(set(missing)):
        print(f'      {n}')
if dirty:
    print(f'  {len(dirty)} resting on extra axioms:')
    for n, ax in dirty:
        print(f'      {n}  {ax}')
if missing or dirty:
    sys.exit(1)
if not ok:
    print('  NOTE: probe build failed for a reason other than a missing constant')
    print('\n'.join(l for l in log.splitlines() if l.startswith('error'))[:800])
    sys.exit(1)
print('  all constants exist and are axiom-clean')
PY
rc=$?
rm -f /tmp/constants_$$.log
exit $rc
