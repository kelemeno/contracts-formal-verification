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
# IT ALSO DETECTS `sorry` AT DECLARATION LEVEL. A declaration proved with `sorry` reports `sorryAx`
# among its axioms, so it shows up as NOT CLEAN. That is sharper than grepping files for the word: it
# names the DECLARATION, ignores `sorry` mentioned in prose, and catches one buried in a single tactic
# block of an otherwise-complete file. As of 2026-08-12 the corpus has 27 (AtomicFlowManager 12,
# L2InteropCommitmentTree 6, L2AssetRouter 5, L2InteropHandler 4, none elsewhere).
#
# NOTE it matches `theorem` AND `lemma`, excluding `private` (which #print axioms cannot reach from
# outside its module). Before 2026-08-12 it matched only `theorem` and silently undercounted.
#
# Exit 0 always; the report is the output. Run from the repo root.
set -u
DIR="${1:-specs/AttackVectors}"
LEDGER="${2:-}"
OUT=/tmp/axsweep-$$
python3 - "$DIR" "$OUT" <<'PY'
import re, sys, glob, os
d, out = sys.argv[1], sys.argv[2]
names, mods, skipped, skipped_dup = [], set(), [], []
for f in sorted(glob.glob(os.path.join(d, '*.lean'))):
    if os.path.basename(f) == 'Audit.lean':
        continue
    # `mcopy.lean` is hand-written under specs/ and COPIED INTO generated/ after each regen
    # (see its own header), so the same constant is provided by two modules and importing both
    # collides. It is not a corpus defect; it just cannot be swept alongside its own copy.
    if os.path.basename(f) == 'mcopy.lean':
        skipped_dup.append(f)
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
        # `lemma` too — it is a theorem by another name, and skipping it silently
        # undercounted every sweep before 2026-08-12. `private` ones are excluded:
        # #print axioms cannot reach them from outside their module.
        m = re.match(r'^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_\'!?]*)', line)
        if m and ns: names.append(f'{ns}.{m.group(1)}')
body = '\n'.join(f'import {m}' for m in sorted(mods))
body += '\n' + '\n'.join(f'#print axioms {n}' for n in names)
open(out + '.lean', 'w').write(body)
print(f'{len(names)} theorems in {len(mods)} modules', file=sys.stderr)
for f in skipped:
    print(f'  SKIPPED (no .olean — never built or does not compile): {f}', file=sys.stderr)
for f in skipped_dup:
    print(f'  SKIPPED (copied into generated/; would collide with its own copy): {f}', file=sys.stderr)
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
if n == 0 and not open(sys.argv[1]).read().strip():
    print('SWEEP FOUND NOTHING: no theorem or lemma declarations parsed in this directory.')
    sys.exit(0)
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
