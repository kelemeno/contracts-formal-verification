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

print(f"total   : {len(clean) + len(dirty)}")
print(f"clean   : {len(clean)}")
print(f"axioms  : {len(dirty)}")
for n, a in sorted(dirty):
    print(f"  {n}")
    for x in sorted(a - base):
        print(f"      {x}")
for u in unparsed:
    print("UNPARSED:", u)
PY
