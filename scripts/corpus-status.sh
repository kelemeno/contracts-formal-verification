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
#
# STUB is the third column and the one this script used to miss: the VC generator emits
# skeletons with `A_<name> := sorry`, and "not an alias" counted them as CLOSED.  That is
# worse than counting an alias as closed -- an alias IS the concrete spec and is sound,
# whereas anything resting on a stub carries `sorryAx`.  InteropHandler read 316 closed
# before this fix; every one of them was a stub.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
python3 - <<'PY'
import os, re
rows=[]; tot_c=tot_a=tot_s=tot_u=0
for c in sorted(os.listdir('specs')):
    base=f'specs/{c}/{c}'
    if not os.path.isdir(base): continue
    files=[]
    for d in (base, base+'/Common'):
        if os.path.isdir(d):
            files += [(d, fn[:-len('_user.lean')]) for fn in os.listdir(d) if fn.endswith('_user.lean')]
    cl=al=un=st=0
    for d,n in files:
        s=open(os.path.join(d,n+'_user.lean')).read()
        hit=False
        for pat in (r'^def A_'+re.escape(n)+r'\b', r'^def AFor_'+re.escape(n)+r'\b'):
            m=re.search(pat+r'.*?:=(.*?)(?=\n\s*\n|\nlemma|\ntheorem|\nend)', s, re.S|re.M)
            if m:
                b=m.group(1).strip()
                if b == 'sorry' or b.startswith('sorry'): st+=1
                elif re.match(r'^'+re.escape(n)+r'_concrete_of_code\.1\b', b) or b=='True': al+=1
                elif 'sorry' in s: st+=1
                else: cl+=1
                hit=True; break
        if not hit: un+=1
    rows.append((c,cl,al,st,un)); tot_c+=cl; tot_a+=al; tot_s+=st; tot_u+=un
w=max(len(r[0]) for r in rows)+2
print(f"{'contract':<{w}}{'closed':>8}{'alias':>8}{'stub':>8}{'unclass':>9}")
for c,cl,al,st,un in sorted(rows,key=lambda r:-r[1]):
    print(f"  {c:<{w-2}}{cl:>8}{al:>8}{st:>8}{un:>9}")
print(f"  {'TOTAL':<{w-2}}{tot_c:>8}{tot_a:>8}{tot_s:>8}{tot_u:>9}")
print()
print("closed = A_<name> is a real definition and the file has no sorry")
print("alias  = A_<name> := <name>_concrete_of_code.1  (sound; costs readable content)")
print("stub   = the file still contains `sorry`  (NOT sound: anything resting on it")
print("         carries sorryAx -- check with scripts/constants-check.sh)")
print("Use scripts/chain-check.sh to ask whether a particular spec RESTS on any alias.")
PY
