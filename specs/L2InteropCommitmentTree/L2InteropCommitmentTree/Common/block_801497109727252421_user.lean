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

Contentful again, at the third attempt.  Two earlier tries failed on the ENCODING rather
than the content, and the shape was finally read off the goal instead of guessed:

  * `add` and `not` produce INSERTS, `and` produces a MULTIFILL -- mixed, not uniform,
    which is what defeated both "all inserts" (4f6e6e7) and "all multifills";
  * `gt` compiles to `if 18446744073709551615 < _ then 1 else 0`, NOT to
    `(decide _).toUInt256` as the sibling comparison blocks use;
  * lookups inside `⟦ ↦ ⟧` need parentheses or the notation mis-parses.

Method worth reusing: `#print` the concrete relation and regex out the repeated subterms,
rather than guessing a shape and reading the type mismatch. -/
def A_block_801497109727252421 (s₀ s₉ : State) : Prop :=
  let b := s₀⟦"split_expr_0" ↦ (s₀["size"]!!) + 31⟧⟦"split_expr_1" ↦ UInt256.lnot 31⟧
  let rounded := Fin.land (b["split_expr_0"]!!) (b["split_expr_1"]!!)
  let c := Clear.State.multifill ["split_expr_2"] [rounded] b
  let d := c⟦"newFreePtr" ↦ (c["memPtr"]!!) + (c["split_expr_2"]!!)⟧
  s₉ = d⟦"split_expr_3" ↦ if 18446744073709551615 < (d["newFreePtr"]!!) then 1 else 0⟧

lemma block_801497109727252421_abs_of_concrete {s₀ s₉ : State} :
  Spec block_801497109727252421_concrete_of_code s₀ s₉ →
  Spec A_block_801497109727252421 s₀ s₉ := by
  unfold block_801497109727252421_concrete_of_code A_block_801497109727252421
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- **THE EVM IS THE CALLER'S.**  Five variable assignments: no memory, no storage, no
hashing.  One equation settles window, flag, accounts and storage together. -/
lemma block_801497109727252421_evm {s₀ s₉ : State}
    (h : A_block_801497109727252421 s₀ s₉) : s₉.evm = s₀.evm := by
  unfold A_block_801497109727252421 at h
  subst h
  simp only [evm_insert, evm_multifill]

end

end L2InteropCommitmentTree.Common
