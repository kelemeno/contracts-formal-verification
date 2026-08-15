#!/usr/bin/env bash
# Run the trust-ledger audit and report the clean/not-clean split.
#
# Why this exists rather than a grep: `#print axioms` emits the axiom list in an
# UNSPECIFIED ORDER and WRAPS long lines.  Grepping for a literal
# "[propext, Classical.choice, Quot.sound]" silently misclassifies clean results
# that happen to print in another order, and drops the tail of every wrapped
# entry.  Both bugs bit real sweeps here.  This parses instead: entries are split
# on the leading quote, re-joined, and the axiom SET is compared against Lean's
# standard base.
#
# Usage: scripts/audit-count.sh [path-to-audit-file]
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
AUDIT="${1:-specs/AttackVectors/Audit.lean}"
OUT=/tmp/audit-count.log

cd "$REPO"
echo "running: lake env lean $AUDIT"
~/.elan/bin/lake env lean "$AUDIT" > "$OUT" 2>&1 || {
  echo "AUDIT FAILED TO ELABORATE — first errors:"
  grep -n "error" -A6 "$OUT" | head -40
  exit 1
}

python3 - "$OUT" <<'PY'
import re, sys
txt = open(sys.argv[1]).read()
base = {'propext', 'Quot.sound', 'Classical.choice'}
clean, dirty, unparsed = [], [], []
for e in re.split(r"\n(?=')", txt):
    e = ' '.join(e.split())
    if not e.startswith("'"):
        continue
    name = e.split("'")[1]
    if 'does not depend on any axioms' in e:
        clean.append((name, set())); continue
    m = re.search(r'depends on axioms: \[(.*?)\]', e)
    if not m:
        unparsed.append(e[:120]); continue
    ax = {a.strip() for a in m.group(1).split(',') if a.strip()}
    (clean if ax <= base else dirty).append((name, ax))

if 'sorryAx' in txt:
    print('!! sorryAx PRESENT — a listed result is not proven')

total = len(clean) + len(dirty)

# A ledger that SHRINKS looks better by every other measure printed here: fewer
# entries, same or higher clean ratio.  Deleting a `#print axioms` line is
# therefore an invisible regression unless the count is pinned.  The baseline
# file records the high-water mark; raise it deliberately when adding entries.
import os
bl_path = os.path.join(os.path.dirname(sys.argv[1]), '') or ''
bl_file = 'specs/AttackVectors/AUDIT_BASELINE'
baseline = None
if os.path.exists(bl_file):
    try:
        baseline = int(open(bl_file).read().split('#')[0].strip())
    except ValueError:
        baseline = None
if baseline is not None and total < baseline:
    print(f"!! LEDGER SHRANK: {total} entries, baseline {baseline}")
    print("!! an entry was removed from Audit.lean, or a name stopped resolving.")
    print("!! this is a regression even though the clean RATIO may have improved.")
    _shrank = True
else:
    _shrank = False

print(f"total   : {total}")
print(f"clean   : {len(clean)}")
print(f"axioms  : {len(dirty)}")
for n, a in sorted(dirty):
    print(f"  {n}")
    for x in sorted(a - base):
        print(f"      {x}")
for u in unparsed:
    print("UNPARSED:", u)
if _shrank:
    sys.exit(1)
PY
