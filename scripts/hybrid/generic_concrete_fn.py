#!/usr/bin/env python3
"""Generic concrete_of_code proof for FUNCTION gens (execCall shape). See generic_concrete.py
for the block (exec) version and the rationale.

Function gen shape:
    def fun_X_concrete_of_code
    : { C : _ → _ → … → State → State → Prop
        // ∀ {s₀ s₉ : State} {a1 a2 … fuel},
             execCall fuel fun_X [r1,…] (s₀, [i1,…]) = s₉ →
             Spec (C a1 a2 …) s₀ s₉
      } := by <fragile script>

Generic witness: C a1 … := fun s₀ s₉ => ∃ fuel, execCall fuel fun_X [r1,…] (s₀, [i1,…]) = s₉
(the operational-semantics relation). Non-Ok cases close with the same `generalize Def _ _ _ = f;
aesop` the working function gens use.

Usage: generic_concrete_fn.py <gen-file.lean>
"""
import re, sys
from pathlib import Path


def patch(path: Path) -> bool:
    t = path.read_text()
    m = re.search(r"def\s+(\w+)_concrete_of_code", t)
    if not m:
        print(f"  ? no concrete_of_code: {path.name}")
        return False
    code = m.group(1)
    by = t.index("} := by", m.start())
    sig = t[m.start():by]
    if "execCall" not in sig:
        print(f"  ! block shape, skip (use generic_concrete.py): {path.name}")
        return False
    # the execCall expression: from 'execCall' up to ' = s₉'
    em = re.search(r"(execCall\s+fuel\s+.+?)\s*=\s*s₉", sig, re.S)
    execexpr = re.sub(r"\s+", " ", em.group(1).strip())
    # C args: from 'Spec (C <args>) s₀ s₉'
    cm = re.search(r"Spec\s*\(\s*C\s+(.+?)\)\s*s₀\s*s₉", sig, re.S)
    cargs = re.sub(r"\s+", " ", cm.group(1).strip())
    ns = re.search(r"^namespace (\S+)", t, re.M).group(1)
    head = t[:by]
    proof = (
        "} := by\n"
        f"  refine ⟨fun {cargs} (s₀ s₉ : State) => ∃ fuel, {execexpr} = s₉, ?_⟩\n"
        f"  intros s₀ s₉ {cargs} fuel\n"
        f"  unfold {code}\n"
        "  unfold Spec\n"
        "  rcases s₀ with ⟨evm, store⟩ | _ | c <;> dsimp only\n"
        "  · intro h _; exact ⟨fuel, h⟩\n"
        "  · generalize Def _ _ _ = f; aesop\n"
        "  · generalize Def _ _ _ = f; aesop\n"
        f"\nend\n\nend {ns}\n"
    )
    path.write_text(head + proof)
    return True


if __name__ == "__main__":
    ok = patch(Path(sys.argv[1]))
    print("patched" if ok else "skipped", sys.argv[1])
