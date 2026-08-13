#!/usr/bin/env bash
# Does a spec rest on anything that is still an ALIAS?
#
# A spec that composes through an alias builds, binds, and keeps its consumer compiling
# -- and says nothing whatever about that step.  None of the other checks here look
# through a composition:
#
#   spec-binds-check.sh  tests a spec's own definition
#   consumer-check.sh    tests that the generated file still compiles
#   loop-content-audit   classifies loops, not the chains under them
#
# So "fun_pushNewLeaf is specced" was claimed while two of its direct branch guards were
# aliases.  They were aliases because the closed versions belonged to a SIBLING COPY of
# the same code -- see scripts/match-copies.sh, which finds those.
#
# This walks the transitive import closure of a spec and reports every alias in it.
# An alias deep in the chain is not always wrong (mcopy cannot be specced at all, and a
# contentless spec is honest about that), but it should be a decision, not a surprise.
#
# Usage: scripts/chain-check.sh <contract> <name> [...]
#        scripts/chain-check.sh L2InteropCommitmentTree fun_pushNewLeaf fun_root
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

CONTRACT="${1:-}"
[ -n "$CONTRACT" ] || { echo "usage: $0 <contract> <name> [...]"; exit 2; }
shift
[ $# -gt 0 ] || { echo "usage: $0 <contract> <name> [...]"; exit 2; }

python3 - "$CONTRACT" "$@" <<'PY'
import sys, os, re

contract = sys.argv[1]
targets = sys.argv[2:]
base = f'specs/{contract}/{contract}'

def path(n):
    for d in (base, base + '/Common'):
        p = os.path.join(d, n + '_user.lean')
        if os.path.isfile(p):
            return p
    return None

def deps_of(n):
    p = path(n)
    if not p:
        return []
    return [l.split('.')[-1].strip() for l in open(p)
            if l.startswith('import generated') and not l.strip().endswith('_gen')]

def is_alias(n):
    p = path(n)
    if not p:
        return None                      # no spec file: nothing to say
    s = open(p).read()
    for pat in (r'^def A_' + re.escape(n) + r'\b', r'^def AFor_' + re.escape(n) + r'\b'):
        m = re.search(pat + r'.*?:=(.*?)(?=\n\s*\n|\nlemma|\ntheorem|\nend)', s, re.S | re.M)
        if m:
            b = m.group(1).strip()
            return bool(re.match(r'^' + re.escape(n) + r'_concrete_of_code\.1\b', b)) or b == 'True'
    return None

bad = 0
for t in targets:
    if path(t) is None:
        print(f"SKIP  {t} (no spec file under {base})")
        continue
    seen, stack, aliases, direct = set(), [(t, 0)], [], set(deps_of(t))
    while stack:
        n, d = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        if is_alias(n) and n != t:
            aliases.append((n, n in direct))
        for x in deps_of(n):
            if x not in seen:
                stack.append((x, d + 1))
    if not aliases:
        print(f"ok    {t}  ({len(seen) - 1} specs beneath it, none an alias)")
    else:
        bad += 1
        print(f"ALIAS {t}  ({len(seen) - 1} beneath it, {len(aliases)} still alias)")
        for n, isdirect in sorted(aliases):
            print(f"        {'DIRECT ' if isdirect else '       '}{n}")

sys.exit(1 if bad else 0)
PY
