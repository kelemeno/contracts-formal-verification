#!/usr/bin/env bash
# Which unfinished loops are BLOCKED by the unmodelled `mcopy` builtin, transitively?
#
# Yul's mcopy has no primop in Clear; the generator emits an empty-bodied stub specced
# `A_mcopy := True` (see AGENTS.md, VC Generator Notes). Nothing composing through it can be
# given an isOk/not_break lemma, so any loop whose dependency CLOSURE reaches mcopy cannot be
# finished from this repo -- the fix is upstream.
#
# Answering this by hand went wrong three times: a regex too narrow, then a `head -8` that cut
# the one dependency that mattered. A truncated search that finds nothing looks exactly like a
# clean one, so this walks the whole closure.
#
# Usage: scripts/loop-mcopy-reach.sh [--list]
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LIST="${1:-}"

LIST="$LIST" python3 - <<'PY'
import re, os, glob, subprocess
gen = glob.glob('generated/**/*_gen.lean', recursive=True)
calls, deps = set(), {}
for g in gen:
    n = os.path.basename(g)[:-len('_gen.lean')]
    src = open(g).read()
    if re.search(r'\bmcopy\(', src): calls.add(n)
    deps[n] = set(re.findall(r'import generated\.[A-Za-z0-9_.]*\.([A-Za-z0-9_]+)$', src, re.M))
def reaches(n, seen=None):
    seen = seen if seen is not None else set()
    if n in seen: return False
    seen.add(n)
    return n in calls or any(reaches(d, seen) for d in deps.get(n, ()))
out = subprocess.run(["./scripts/loop-content-audit.sh","--list"],capture_output=True,text=True).stdout
loops = sorted({os.path.basename(l.strip())[:-len('_user.lean')]
                for sec in ("TRUE-FOR:","PARTIAL:")
                for l in out.split(sec)[1].splitlines() if l.strip().endswith('.lean')})
blocked = [l for l in loops if reaches(l)]
free    = [l for l in loops if l not in blocked]
print(f"unfinished loops: {len(loops)}")
print(f"  blocked by mcopy : {len(blocked)}  (not finishable from this repo)")
print(f"  mcopy-free       : {len(free)}  (workable)")
if os.environ.get("LIST") == "--list":
    print("\nWORKABLE:");  [print("   ", l) for l in free]
    print("\nBLOCKED:");   [print("   ", l) for l in blocked]
PY
