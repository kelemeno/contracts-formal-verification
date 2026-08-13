#!/usr/bin/env bash
# Corpus-wide status: how many specs per contract say something, and how many are aliases.
#
# `grep -L sorry` and green builds both lie here (see AGENTS.md), so the only honest
# per-spec question is whether its `A_<name>` is a real definition or an alias to
# `<name>_concrete_of_code.1`.  This counts that, per contract.
#
# Specs whose definition does not match the `A_<name>` / `AFor_<name>` convention are
# reported as UNCLASSIFIED rather than silently counted either way -- some hand-written
# specs use their own names, and lumping them in would inflate whichever column.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
python3 - <<'PY'
import os, re
rows=[]; tot_c=tot_a=tot_u=0
for c in sorted(os.listdir('specs')):
    base=f'specs/{c}/{c}'
    if not os.path.isdir(base): continue
    files=[]
    for d in (base, base+'/Common'):
        if os.path.isdir(d):
            files += [(d, fn[:-len('_user.lean')]) for fn in os.listdir(d) if fn.endswith('_user.lean')]
    cl=al=un=0
    for d,n in files:
        s=open(os.path.join(d,n+'_user.lean')).read()
        hit=False
        for pat in (r'^def A_'+re.escape(n)+r'\b', r'^def AFor_'+re.escape(n)+r'\b'):
            m=re.search(pat+r'.*?:=(.*?)(?=\n\s*\n|\nlemma|\ntheorem|\nend)', s, re.S|re.M)
            if m:
                b=m.group(1).strip()
                if re.match(r'^'+re.escape(n)+r'_concrete_of_code\.1\b', b) or b=='True': al+=1
                else: cl+=1
                hit=True; break
        if not hit: un+=1
    rows.append((c,cl,al,un)); tot_c+=cl; tot_a+=al; tot_u+=un
w=max(len(r[0]) for r in rows)+2
print(f"{'contract':<{w}}{'closed':>8}{'alias':>8}{'unclass':>9}")
for c,cl,al,un in sorted(rows,key=lambda r:-r[1]):
    print(f"  {c:<{w-2}}{cl:>8}{al:>8}{un:>9}")
print(f"  {'TOTAL':<{w-2}}{tot_c:>8}{tot_a:>8}{tot_u:>9}")
print()
print("closed = A_<name> is a real definition; alias = A_<name> := <name>_concrete_of_code.1")
print("Use scripts/chain-check.sh to ask whether a particular spec RESTS on any alias.")
PY
