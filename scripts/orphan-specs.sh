#!/usr/bin/env bash
# Find spec files that no check in this corpus can see.
#
# WHY THIS EXISTS.  Every verification metric here is reachability-based:
# `#print axioms` needs the constant imported, and `lake build` only covers a
# target's dependency cone.  So a spec file that nothing imports is not
# "unverified pending a check" — it is OUTSIDE the reach of every check that
# exists, and can sit BROKEN indefinitely while all reported numbers stay green.
#
# Not hypothetical: imt_root_atlas_user.lean (~76 results, the entire R0–R3 root
# track) appeared in neither Specs.lean nor Audit.lean.  It sat broken with a
# dangling reference (`byte_mstore32_pinned`, a deleted helper) for an unknown
# stretch and was found by accident.  Fixed 2026-08-17 by importing it into the
# ledger; this script is so the next one is found on purpose.
#
# Two reachability roots, because they catch different failures:
#   Specs.lean  — the build aggregate.  Reachable => it COMPILES.  Catches
#                 dangling references, type errors, `sorry` via the linter.
#   Audit.lean  — the trust ledger.  Reachable => `#print axioms` can name it.
#                 Compiling is not the same as being axiom-clean.
#
# Hence two classes, in decreasing severity:
#   UNBUILT  — in neither.  Nothing checks these at all.  Always a bug.
#   UNAUDITED— builds, but its results never reach the ledger.  Expected for
#              the auto-generated Common/ block stubs (thousands of them, and
#              ~98% are tautological `A := concrete` aliases anyway); worth a
#              look for anything hand-written.
#
# Usage: scripts/orphan-specs.sh [--all]    (--all lists UNAUDITED in full)
# Exit 1 if any UNBUILT file exists, else 0.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"

python3 - "${1:-}" <<'PY'
import os, re, sys

show_all = (len(sys.argv) > 1 and sys.argv[1] == '--all')

BUILD_ROOT = 'Specs.lean'          # lakefile: lean_lib specs, roots := #[`specs]
LEDGER_ROOT = 'specs/AttackVectors/Audit.lean'

on_disk = set()
for dirpath, _, files in os.walk('specs'):
    for f in files:
        if f.endswith('.lean'):
            on_disk.add(os.path.join(dirpath, f))

imp_re = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)', re.M)

def closure(root):
    seen, stack = set(), [root]
    while stack:
        p = stack.pop()
        if p in seen or not os.path.exists(p):
            continue
        seen.add(p)
        for m in imp_re.findall(open(p, encoding='utf-8').read()):
            if m.startswith('specs.'):
                stack.append(m.replace('.', '/') + '.lean')
    return seen

for r in (BUILD_ROOT, LEDGER_ROOT):
    if not os.path.exists(r):
        print(f"cannot find root {r}"); sys.exit(2)

built  = closure(BUILD_ROOT)  & on_disk
audited = closure(LEDGER_ROOT) & on_disk

unbuilt   = sorted(on_disk - built - audited)
unaudited = sorted(built - audited)

# the auto-generated per-block stubs are the expected bulk of UNAUDITED
def is_stub(p):
    return '/Common/' in p and re.search(r'/(block|if|switch|for)_\d+_user\.lean$', p)

hand_unaudited = [p for p in unaudited if not is_stub(p)]

print(f"spec files on disk : {len(on_disk)}")
print(f"built  (Specs.lean): {len(built)}")
print(f"audited (Audit.lean): {len(audited)}")
print()
print(f"UNBUILT  (in NEITHER — nothing checks these) : {len(unbuilt)}")
for p in unbuilt:
    print(f"  {p}")
print()
print(f"UNAUDITED (build, but never reach the ledger): {len(unaudited)}"
      f"  [{len(unaudited) - len(hand_unaudited)} auto-generated stubs,"
      f" {len(hand_unaudited)} hand-written]")
for p in (unaudited if show_all else hand_unaudited):
    print(f"  {p}")
if not show_all and len(unaudited) > len(hand_unaudited):
    print("  (stubs hidden; re-run with --all to list them)")

sys.exit(1 if unbuilt else 0)
PY
