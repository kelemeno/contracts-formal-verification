#!/usr/bin/env bash
# Find which ALREADY-CLOSED spec an open block/switch/if corresponds to.
#
# solc emits the same code many times over -- once per call site or per type
# instantiation -- and gives each copy an unrelated id.  So a block you have already
# specced reappears as `block_3834594906904189566` with no hint that it is the same
# code as `block_5648918763415424361`.  Chasing that by eye is how you end up
# re-deriving a spec you already have, or worse, porting onto the wrong copy.
#
# This hashes each generated body with the things that differ between copies
# normalised away:
#   * the accessor variant suffixes (_dyn_ptr / _dyn__dyn), which name the same code
#   * every block/switch/if/for id inside the body
# and reports open ids whose normalised body matches a closed one.
#
# A match means the spec can be ported by id substitution -- but check the REFERENCES
# too: a ported outer switch still names the inner switch by the SOURCE copy's id, and
# the dependency counts do not show that.
#
# Usage: scripts/match-copies.sh <contract> [id ...]
#   with no ids, reports every open id in the contract that matches a closed one.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

CONTRACT="${1:-}"
[ -n "$CONTRACT" ] || { echo "usage: $0 <contract> [id ...]"; exit 2; }
shift || true

python3 - "$CONTRACT" "$@" <<'PY'
import sys, os, re

contract = sys.argv[1]
wanted = set(sys.argv[2:])
gen = f'generated/{contract}/{contract}/Common'
spec = f'specs/{contract}/{contract}/Common'
if not os.path.isdir(gen):
    print(f"no Common directory for {contract}")
    sys.exit(2)

def normalised_body(name):
    p = os.path.join(gen, name + '_gen.lean')
    if not os.path.isfile(p):
        return None
    try:
        t = open(p, errors='ignore').read()
    except OSError:
        return None
    m = re.search(r'^def ' + re.escape(name) + r' :=.*?\n(.*?)^>', t, re.S | re.M)
    if not m:
        return None
    b = m.group(1)
    b = b.replace('_dyn_ptr', '_ACC').replace('_dyn__dyn', '_ACC')
    b = re.sub(r'\b(block|switch|if|for)_\d+\b', 'ID', b)
    return b

def is_alias(name):
    p = os.path.join(spec, name + '_user.lean')
    if not os.path.isfile(p):
        return None
    s = open(p).read()
    for pat in (r'^def A_' + re.escape(name) + r'\b', r'^def AFor_' + re.escape(name) + r'\b'):
        m = re.search(pat + r'.*?:=(.*?)(?=\n\s*\n|\nlemma|\ntheorem|\nend)', s, re.S | re.M)
        if m:
            body = m.group(1).strip()
            return bool(re.match(r'^' + re.escape(name) + r'_concrete_of_code\.1\b', body)) or body == 'True'
    return None

names = [fn[:-len('_gen.lean')] for fn in os.listdir(gen) if fn.endswith('_gen.lean')]
closed, openish = {}, {}
for n in names:
    a = is_alias(n)
    if a is None:
        continue
    b = normalised_body(n)
    if b is None:
        continue
    (openish if a else closed).setdefault(b, []).append(n)

rows = []
for b, ns in openish.items():
    if b in closed:
        for n in ns:
            if not wanted or n in wanted:
                rows.append((n, closed[b][0]))

if not rows:
    # "no match" from a text-matching checker is worthless unless the matcher is known
    # to match SOMETHING, so report the closed-vs-closed duplicate groups as evidence
    # that the normalisation works.  Those groups are the ports already done.
    dup = [ns for ns in closed.values() if len(ns) > 1]
    print(f"{contract}: no open id matches a closed spec" +
          (f" among {sorted(wanted)}" if wanted else ""))
    print(f"  ({len(names)} defs read, {sum(len(v) for v in closed.values())} closed, "
          f"{sum(len(v) for v in openish.values())} open; "
          f"{len(dup)} group(s) of CLOSED specs share a normalised body, which is the "
          f"matcher working -- those are copies already ported)")
else:
    print(f"{contract}: {len(rows)} open id(s) match an already-closed spec")
    for n, c in sorted(rows):
        print(f"  {n:<34} <- {c}")
    print()
    print("port by substituting the id (and the accessor variant if it differs),")
    print("then check the ported text for references to the SOURCE copy's other ids")
PY
