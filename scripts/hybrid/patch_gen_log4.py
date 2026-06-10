#!/usr/bin/env python3
"""Patch the broken `rw [EVMLog4']` in generated _gen.lean files so they build.

Clear's `EVMLog4'` lemma is mis-stated (Clear/Clear/PrimOps.lean):
    lemma EVMLog4' : primCall s .Log4 [] = (s, []) := rfl
The empty arg list is a typo (Log1=3, Log2=4, Log3=5 args, so Log4 needs 6).
The VC generator emits `primCall s .Log4 [v1,v2,v3,v4,v5,v6]`, so `rw [EVMLog4']`
fails to unify (the LHS pattern has the wrong arity).

`primCall` has a catch-all `| _, _ => (s, [])`, so the 6-arg Log4 call still
reduces to `(s, [])` definitionally. We replace the failing `rw [EVMLog4']` with
`simp only [primCall]`, which unfolds primCall and discharges the goal via the
catch-all (verified by experiment on fun_bridgehubDepositNonBaseTokenAsset_gen.lean).

Idempotent + reusable: generated/ is gitignored and wiped by generate-vc, so re-run
this after regenerating. Patches both generated/ and Clear/Generated/ copies.

Usage: scripts/hybrid/patch_gen_log4.py
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DIRS = [ROOT / "generated", ROOT / "Clear" / "Generated"]

OLD = "rw [EVMLog4']"
NEW = "simp only [primCall]"


def main():
    patched_files = 0
    patched_lines = 0
    for d in DIRS:
        if not d.exists():
            continue
        for f in d.rglob("*_gen.lean"):
            txt = f.read_text()
            if OLD not in txt:
                continue
            n = txt.count(OLD)
            new = txt.replace(OLD, NEW)
            f.write_text(new)
            patched_files += 1
            patched_lines += n
            print(f"  patched {n} EVMLog4' call(s) in {f.relative_to(ROOT)}")
    print(f"\nDONE. files patched: {patched_files}, EVMLog4' rewrites replaced: {patched_lines}")


if __name__ == "__main__":
    main()
