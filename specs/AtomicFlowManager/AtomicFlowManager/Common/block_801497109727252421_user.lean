import Clear.ReasoningPrinciple
import specs.StateOk


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_801497109727252421_gen


namespace AtomicFlowManager.Common

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
`if_5792510925045852942` together with the wraparound flag. -/
def A_block_801497109727252421 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"split_expr_0" ↦ s₀["size"]!! + 31⟧
  let b := a⟦"split_expr_1" ↦ UInt256.lnot 31⟧
  let c := b⟦"split_expr_2" ↦ Fin.land (b["split_expr_0"]!!) (b["split_expr_1"]!!)⟧
  let d := c⟦"newFreePtr" ↦ c["memPtr"]!! + (c["split_expr_2"]!!)⟧
  s₉ = d⟦"split_expr_3" ↦ if 18446744073709551615 < d["newFreePtr"]!! then 1 else 0⟧

lemma block_801497109727252421_abs_of_concrete {s₀ s₉ : State} :
  Spec block_801497109727252421_concrete_of_code s₀ s₉ →
  Spec A_block_801497109727252421 s₀ s₉ := by
  unfold block_801497109727252421_concrete_of_code A_block_801497109727252421
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_801497109727252421_isOk {s₀ s₉ : State} (hok : isOk s₀) (h : A_block_801497109727252421 s₀ s₉) : isOk s₉ := by
  rw [h]; simp only [isOk_insert]; exact hok

lemma block_801497109727252421_not_break {s₀ s₉ : State} (hok : isOk s₀) (h : A_block_801497109727252421 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_801497109727252421_isOk hok h)

end

end AtomicFlowManager.Common
