#!/usr/bin/env python3
"""Apply the thin-wrapper proof to Common control-flow block stubs (if_/for_/switch_).

Each such stub has the shape:
    def A_<name> <binders> : Prop := sorry
    lemma <name>_abs_of_concrete ... :
      Spec <CONCRETE-EXPR> s₀ s₉ →
      Spec (A_<name> <args>) s₀ s₉ := by
      sorry

The thin-wrapper makes A_<name> definitionally equal to the concrete spec, so the
abs_of_concrete lemma is just `intro h; simpa [A_<name>] using h`. We extract the exact
<CONCRETE-EXPR> from the lemma hypothesis (handles both `Foo_concrete_of_code` and
`Foo_concrete_of_code.1 a b c`), set the def body to `<CONCRETE-EXPR> s₀ s₉`, and replace
the lemma's `sorry` with the wrapper proof.

This does NOT build — caller verifies with lake. Reverts nothing; idempotent on already-wrapped
files (skips files without `:= sorry`).

Usage: scripts/hybrid/thin_wrap_common.py [Contract]   (default L1Bridgehub)
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

HYP = re.compile(r"Spec\s+(.+?)\s+s₀\s+s₉\s*→", re.S)
CONCL = re.compile(r"Spec\s+\(?\s*(A_[A-Za-z0-9_]+)")


def main():
    contract = sys.argv[1] if len(sys.argv) > 1 else "L1Bridgehub"
    base = ROOT / "specs" / contract / contract / "Common"
    # Only if_/switch_ have the single-def single-lemma thin-wrappable shape.
    # for_ blocks have a multi-def loop structure (ACond/APost/ABody/AFor) — handled separately.
    files = (sorted(base.glob("if_*_user.lean"))
             + sorted(base.glob("switch_*_user.lean"))
             + sorted(base.glob("block_*_user.lean")))
    done = skipped = failed = 0
    for f in files:
        txt = f.read_text()
        if "sorry" not in txt:
            continue
        defm = re.search(r"(def\s+(A_[A-Za-z0-9_]+)\b[^\n]*?:\s*Prop\s*:=)\s*sorry", txt)
        if not defm:
            print(f"  ? no def-sorry: {f.name}")
            skipped += 1
            continue
        aname = defm.group(2)
        hyp = HYP.search(txt)
        if not hyp:
            print(f"  ? no hyp: {f.name}")
            skipped += 1
            continue
        concrete = hyp.group(1).strip()
        # strip an outer paren pair if present
        if concrete.startswith("(") and concrete.endswith(")"):
            concrete = concrete[1:-1].strip()
        # concrete_of_code is a sigma ⟨code, proof⟩; `.1` extracts the code (then coerced).
        # The lemma hypothesis writes it bare (Spec uses an instance coercion); the def needs `.1`.
        proj = concrete if concrete.endswith(".1") or ".1 " in concrete else concrete + ".1"
        new_def = f"{defm.group(1)} {proj} s₀ s₉"
        new = txt[:defm.start()] + new_def + txt[defm.end():]
        # replace the lemma-body sorry (the remaining standalone `sorry`)
        # it is the last `sorry` token in the file
        idx = new.rfind("sorry")
        if idx == -1:
            print(f"  ? no lemma sorry: {f.name}")
            failed += 1
            continue
        new = new[:idx] + f"intro h\n  simpa [{aname}] using h" + new[idx + len("sorry"):]
        f.write_text(new)
        done += 1
    print(f"\nDONE. wrapped: {done}, skipped: {skipped}, failed: {failed}")


if __name__ == "__main__":
    main()
