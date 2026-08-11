#!/usr/bin/env bash
# Axiom sweep: print every theorem in a spec directory that depends on a NON-KERNEL axiom.
#
# The Audit ledger is hand-maintained, so its denominator is a coverage claim, not a fact —
# a theorem nobody thought to add is silently absent. This sweep checks the ledger's coverage
# by enumerating theorems directly from the source.
#
#   ./scripts/axiom-sweep.sh specs/AttackVectors        # sweep a directory
#   ./scripts/axiom-sweep.sh specs/AttackVectors Audit  # ...and flag ones the ledger omits
#
# Exit 0 always; the report is the output. Run from the repo root.
set -u
DIR="${1:-specs/AttackVectors}"
LEDGER="${2:-}"
OUT=/tmp/axsweep-$$
python3 - "$DIR" "$OUT" <<'PY'
import re, sys, glob, os
d, out = sys.argv[1], sys.argv[2]
names, mods, skipped = [], set(), []
for f in sorted(glob.glob(os.path.join(d, '*.lean'))):
    if os.path.basename(f) == 'Audit.lean':
        continue
    # Skip modules with no .olean: one unbuilt file aborts the whole import and would
    # otherwise take the entire sweep down with it. Report them rather than hiding them.
    olean = os.path.join('.lake/build/lib', f[:-5] + '.olean')
    if not os.path.exists(olean):
        skipped.append(f)
        continue
    mods.add(f[:-5].replace('/', '.'))
    ns = None
    for line in open(f):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m: ns = m.group(1)
        m = re.match(r'^theorem\s+([A-Za-z_][A-Za-z0-9_\'!?]*)', line)
        if m and ns: names.append(f'{ns}.{m.group(1)}')
body = '\n'.join(f'import {m}' for m in sorted(mods))
body += '\n' + '\n'.join(f'#print axioms {n}' for n in names)
open(out + '.lean', 'w').write(body)
print(f'{len(names)} theorems in {len(mods)} modules', file=sys.stderr)
for f in skipped:
    print(f'  SKIPPED (no .olean — never built or does not compile): {f}', file=sys.stderr)
PY
cp "$OUT.lean" specs/AxSweepTmp.lean
~/.elan/bin/lake env ~/.elan/toolchains/leanprover--lean4---v4.9.1/bin/lean specs/AxSweepTmp.lean > "$OUT.txt" 2>&1
rm -f specs/AxSweepTmp.lean "$OUT.lean"
python3 - "$OUT.txt" "$LEDGER" <<'PY'
import re, sys
t = re.sub(r'\n\s+', ' ', open(sys.argv[1]).read())
ledger = ''
if len(sys.argv) > 2 and sys.argv[2]:
    import glob
    for f in glob.glob(f'specs/**/{sys.argv[2]}.lean', recursive=True):
        ledger += open(f).read()
n = clean = 0
bad = []
for l in t.split('\n'):
    if 'depends on axioms' in l:
        n += 1
        nm = l.split("'")[1]
        ex = [a.strip().split('.')[-1] for a in l.split('[')[1].rstrip(']').split(',')
              if a.strip() not in ('propext', 'Quot.sound', 'Classical.choice')]
        if ex: bad.append((nm, ex))
        else: clean += 1
    elif 'does not depend on any axioms' in l:
        n += 1; clean += 1
if n == 0:
    print('SWEEP FAILED: no theorem printed its axioms.')
    print('  A module in this directory almost certainly failed to import — one broken file')
    print('  aborts the whole run, and a silent "0 clean of 0" reads like "nothing to check".')
    print('  First lines of the Lean output:')
    for line in open(sys.argv[1]).read().split('\n')[:6]:
        if line.strip(): print('   ', line)
    sys.exit(0)
print(f'{clean} clean of {n}')
for nm, ex in bad:
    short = nm.split('.')[-1]
    tag = '' if not ledger else ('  [in ledger]' if short in ledger else '  [*NOT IN LEDGER*]')
    print(f'  NOT CLEAN: {short} -> {",".join(ex)}{tag}')
PY
rm -f "$OUT.txt"
