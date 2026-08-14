import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_801497109727252421_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Round the allocation size up to a word, and bound-check the new free pointer.**

```
    split_expr_2 := and(size + 31, not(31))   -- round up to 32
    newFreePtr := memPtr + split_expr_2
    split_expr_3 := gt(newFreePtr, 0xffffffffffffffff)
```

`and(x + 31, not(31))` is the standard round-to-word, and the flag records whether the
new free pointer passes solc's `2^64 - 1` memory ceiling -- checked by
`if_5792510925045852942` together with the wraparound flag.

REVERTED TO AN ALIAS.  A contentful version was committed in 4f6e6e7 and NEVER COMPILED:
it wrote every step as an insert, but the `and` primop produces a `multifill`, so
`abs_of_concrete` could not close.  The breakage survived because that commit's own
subject -- a shell bug reporting false greens -- was the bug that hid it, and afterwards a
stale olean kept the module reporting OK.  Found by scripts/constants-check.sh, which
looks the CONSTANTS up instead of trusting the module build.

Re-converting it needs the `and` step written as `multifill ["split_expr_2"] [...]`; the
docstring above is the intended content. -/
def A_block_801497109727252421 (s₀ s₉ : State) : Prop := block_801497109727252421_concrete_of_code.1 s₀ s₉

lemma block_801497109727252421_abs_of_concrete {s₀ s₉ : State} :
  Spec block_801497109727252421_concrete_of_code s₀ s₉ →
  Spec A_block_801497109727252421 s₀ s₉ := by
  intro h
  simpa [A_block_801497109727252421] using h

end

end L2InteropCommitmentTree.Common
