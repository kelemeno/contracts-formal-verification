#!/usr/bin/env python3
"""Thin-wrap `for_` Common block stubs (the multi-def loop shape).

Mirrors the committed hand pattern (e.g. L1Bridgehub Common/for_1639041582502888472_user.lean):
weak `True` specs for APost/ABody/AFor, an exact ACond extracted from the gen file's
`for_<id>_cond` quotation, and the standard AZero/AOk/AContinue/ABreak/ALeave boilerplate.

Handles cond shapes:  `lt(a, b)`  ->  fromBool (s₀["a"]!! < s₀["b"]!!)   (EVMLt')
                      `1`         ->  (1 : Literal)

Usage: thin_wrap_for.py <Contract>
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

TEMPLATE_COND_LT = '''def ACond_{n} (s₀ : State) : Literal := fromBool (s₀["{a}"]!! < s₀["{b}"]!!)'''
PROOF_COND_LT = '''  unfold eval ACond_{n}
  simp [{n}_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]'''

TEMPLATE_COND_ONE = '''def ACond_{n} (s₀ : State) : Literal := 1'''
PROOF_COND_ONE = '''  unfold eval ACond_{n}
  simp [{n}_cond, Lit']'''


def wrap(f: Path, contract: str) -> bool:
    txt = f.read_text()
    if "sorry" not in txt:
        return False
    n = f.name.replace("_user.lean", "")
    gen = ROOT / "generated" / contract / contract / "Common" / f"{n}_gen.lean"
    m = re.search(r"def " + n + r"_cond := <<\s*(.+?)\s*>>", gen.read_text(), re.S)
    if not m:
        print(f"  ? no cond found: {n}")
        return False
    cond = m.group(1).strip()
    mlt = re.fullmatch(r"lt\((\w+),\s*(\w+)\)", cond)
    if mlt:
        cond_def = TEMPLATE_COND_LT.format(n=n, a=mlt.group(1), b=mlt.group(2))
        cond_proof = PROOF_COND_LT.format(n=n)
    elif cond == "1":
        cond_def = TEMPLATE_COND_ONE.format(n=n)
        cond_proof = PROOF_COND_ONE.format(n=n)
    else:
        print(f"  ? unsupported cond `{cond}`: {n}")
        return False

    txt = txt.replace(f"def ACond_{n} (s₀ : State) : Literal := sorry \n", cond_def + "\n")
    txt = txt.replace(f"def ACond_{n} (s₀ : State) : Literal := sorry\n", cond_def + "\n")
    txt = txt.replace(f"def APost_{n} (s₀ s₉ : State) : Prop := sorry",
                      f"def APost_{n} (s₀ s₉ : State) : Prop := True")
    txt = txt.replace(f"def ABody_{n} (s₀ s₉ : State) : Prop := sorry",
                      f"def ABody_{n} (s₀ s₉ : State) : Prop := True")
    txt = txt.replace(f"def AFor_{n} (s₀ s₉ : State) : Prop := True" if False else
                      f"def AFor_{n} (s₀ s₉ : State) : Prop := sorry",
                      f"def AFor_{n} (s₀ s₉ : State) : Prop := True")
    # cond lemma proof
    txt = txt.replace(f"  unfold eval ACond_{n}\n  sorry", cond_proof)
    # post/body abs lemmas
    txt = txt.replace(
        f"Spec APost_{n} s₀ s₉ := by\n  sorry",
        f"Spec APost_{n} s₀ s₉ := by\n  unfold APost_{n}\n"
        "  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec")
    txt = txt.replace(
        f"Spec ABody_{n} s₀ s₉ := by\n  sorry",
        f"Spec ABody_{n} s₀ s₉ := by\n  unfold ABody_{n}\n"
        "  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec")
    # boilerplate closers
    txt = txt.replace(f"AFor_{n} s₀ s₀ := sorry",
                      f"AFor_{n} s₀ s₀ := by\n  intro s₀ _ _\n  trivial")
    txt = txt.replace(f"AFor_{n} s₀ s₅\n:= sorry",
                      f"AFor_{n} s₀ s₅\n:= by\n  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _ _\n  trivial")
    txt = txt.replace(f"Spec AFor_{n} s₄ s₅ → AFor_{n} s₀ s₅ := sorry",
                      f"Spec AFor_{n} s₄ s₅ → AFor_{n} s₀ s₅ := by\n"
                      "  intro s₀ s₂ s₄ s₅ _ _ _ _ _ _\n  trivial")
    txt = txt.replace(f"AFor_{n} s₀ (🧟s₂) := sorry",
                      f"AFor_{n} s₀ (🧟s₂) := by\n  intro s₀ s₂ _ _ _ _\n  trivial")
    txt = txt.replace(f"AFor_{n} s₀ s₂ := sorry",
                      f"AFor_{n} s₀ s₂ := by\n  intro s₀ s₂ _ _ _ _\n  trivial")
    if "sorry" in txt:
        print(f"  ! residual sorry: {n}")
    f.write_text(txt)
    return True


def main():
    contract = sys.argv[1]
    base = ROOT / "specs" / contract / contract / "Common"
    done = 0
    for f in sorted(base.glob("for_*_user.lean")):
        if wrap(f, contract):
            done += 1
    print(f"DONE. wrapped: {done}")


if __name__ == "__main__":
    main()
