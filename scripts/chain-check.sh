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
# This walks the transitive import closure of a spec and reports every alias in it -- and
# every STUB, which is the more urgent case: a stub is `A_x := sorry`, so anything above it
# carries `sorryAx` and proves NOTHING.  Two specs were found in that state on 2026-08-14
# (one of them an access-control guard), each sorry-free in its own file with the `sorry`
# several imports away.  Aliases cost readability; stubs cost soundness.
# WHAT THIS DOES AND DOES NOT MEAN.  `A_x := x_concrete_of_code.1` IS the concrete spec,
# so composing through an alias is not unsound and does not make a result vacuous -- a
# theorem proved through aliases is still a theorem about the compiled code.  What an
# alias costs is READABLE CONTENT: nothing can be stated about that step in abstract
# terms, so a caller's spec is silent about it.  That is why it mattered for
# fun_pushNewLeaf (whose spec is meant to describe the branches) and matters less for a
# result that is about the concrete spec anyway.
#
# Also: this walks the IMPORT CLOSURE, not the proof term.  A file can import a spec its
# key theorem never uses, so an ALIAS verdict is "content is missing somewhere in this
# chain", not "this result depends on an unspecified step".  For what a result actually
# depends on, read `#print axioms` (scripts/audit-count.sh).
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

def is_stub(n):
    p = path(n)
    if not p:
        return False
    return 'sorry' in open(p).read()

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
    seen, stack, aliases, stubs, direct = set(), [(t, 0)], [], [], set(deps_of(t))
    while stack:
        n, d = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        if is_stub(n) and n != t:
            stubs.append((n, n in direct))
        elif is_alias(n) and n != t:
            aliases.append((n, n in direct))
        for x in deps_of(n):
            if x not in seen:
                stack.append((x, d + 1))
    if stubs:
        bad += 1
        print(f"STUB  {t}  ({len(seen) - 1} beneath it, {len(stubs)} STUB -- this proves NOTHING)")
        for n, isdirect in sorted(stubs):
            print(f"        {'DIRECT ' if isdirect else '       '}{n}")
        if aliases:
            print(f"      (also {len(aliases)} alias)")
    elif not aliases:
        print(f"ok    {t}  ({len(seen) - 1} specs beneath it, no stub and no alias)")
    else:
        bad += 1
        print(f"ALIAS {t}  ({len(seen) - 1} beneath it, {len(aliases)} still alias)")
        for n, isdirect in sorted(aliases):
            print(f"        {'DIRECT ' if isdirect else '       '}{n}")

sys.exit(1 if bad else 0)
PY
