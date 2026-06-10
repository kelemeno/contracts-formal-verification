#!/usr/bin/env python3
"""Patch unquoted Solidity revert strings in generated _gen.lean files so they parse.

Clear's YulNotation `expr` grammar has no string-literal case, but the VC generator emits
`mstore(ptr, Some revert: message)` with the message UNQUOTED → Lean parse error
(`unexpected token ':'`). The revert-message TEXT is irrelevant to verification (it's a
revert-branch error string), so we replace the bad argument with `0`.

Idempotent + reusable: generated/ is gitignored and wiped by generate-vc, so re-run this after
regenerating. Patches both generated/ and Clear/Generated/ copies.

Usage: scripts/hybrid/patch_gen_strings.py
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DIRS = [ROOT / "generated", ROOT / "Clear" / "Generated"]

# mstore(<arg1>, <arg2>) where arg2 is bare text (has a space or ':') and is NOT a nested call.
MSTORE = re.compile(r"(mstore\([^,]+,\s*)([^)]*)\)")


def fix_arg(m):
    pre, arg = m.group(1), m.group(2)
    a = arg.strip()
    if "(" not in a and (":" in a or " " in a):  # unquoted revert string, not a call/number/ident
        return pre + "0)"
    return m.group(0)


def main():
    patched_files = 0
    patched_lines = 0
    for d in DIRS:
        if not d.exists():
            continue
        for f in d.rglob("*_gen.lean"):
            txt = f.read_text()
            new, n = MSTORE.subn(fix_arg, txt)
            if n and new != txt:
                # count only the lines that actually changed
                changed = sum(1 for a, b in zip(txt.splitlines(), new.splitlines()) if a != b)
                f.write_text(new)
                patched_files += 1
                patched_lines += changed
                print(f"  patched {changed} revert-string(s) in {f.relative_to(ROOT)}")
    print(f"\nDONE. files patched: {patched_files}, revert-strings replaced: {patched_lines}")


if __name__ == "__main__":
    main()
