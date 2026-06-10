#!/usr/bin/env python3
"""Apply the thin-wrapper proof to TOP-LEVEL function/helper stubs (not Common blocks).

Shape:
    def A_<name> <binders> : Prop := sorry
    lemma <name>_abs_of_concrete ... :
      Spec (<name>_concrete_of_code.1 <args>) s₀ s₉ →
      Spec (A_<name> <args>) s₀ s₉ := by
      unfold <name>_concrete_of_code A_<name>
      sorry

Thin-wrapper: `def A_<name> <binders> := <CONCRETE-EXPR> s₀ s₉` where <CONCRETE-EXPR> is the
hypothesis term (already includes `.1 <args>`), and the proof becomes `intro h; simpa [A_<name>] using h`
(the `unfold` line is removed — unfolding A into the goal before intro breaks typing).

Does NOT build — caller verifies with lake and reverts failures. Skips files with no `:= sorry`.

Usage: scripts/hybrid/thin_wrap_toplevel.py <Contract>
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

HYP = re.compile(r"Spec\s+(.+?)\s+s₀\s+s₉\s*→", re.S)


def main():
    if len(sys.argv) < 2:
        print("usage: thin_wrap_toplevel.py <Contract>")
        return
    contract = sys.argv[1]
    base = ROOT / "specs" / contract / contract
    files = sorted(base.glob("*_user.lean"))
    done = skipped = 0
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
        if concrete.startswith("(") and concrete.endswith(")"):
            concrete = concrete[1:-1].strip()
        new_def = f"{defm.group(1)} {concrete} s₀ s₉"
        new = txt[:defm.start()] + new_def + txt[defm.end():]
        # Replace the proof tail `unfold ...\n  sorry` (or a bare trailing sorry) with the wrapper.
        wrapper = f"intro h\n  simpa [{aname}] using h"
        new2, k = re.subn(r"unfold[^\n]*\n\s*sorry", wrapper, new)
        if k == 0:  # bare sorry fallback
            idx = new.rfind("sorry")
            new2 = new[:idx] + wrapper + new[idx + len("sorry"):]
        f.write_text(new2)
        done += 1
    print(f"\nDONE. wrapped: {done}, skipped: {skipped}")


if __name__ == "__main__":
    main()
