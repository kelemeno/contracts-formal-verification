import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Apply the mask and store**, second half:

```
    split_expr_3 := and(_1, split_expr_2)      -- old word, field cleared
    split_expr_4 := shl(shiftBits, value)      -- value in position
    sstore(slot, or(split_expr_3, split_expr_4))
```

So the slot's other fields survive and the field takes `value`.  With `offset = 0`
(the `bytes32` case) the cleared word is `0` and this stores `value` outright. -/
def A_block_8692170500034331446 (s₀ s₉ : State) : Prop :=
  let a := Clear.State.multifill ["split_expr_3"]
    [Fin.land (s₀["_1"]!!) (s₀["split_expr_2"]!!)] s₀
  let b := Clear.State.multifill ["split_expr_4"]
    [Fin.shiftLeft (a["value"]!!) (a["shiftBits"]!!)] a
  let c := Clear.State.multifill ["split_expr_5"]
    [Fin.lor (b["split_expr_3"]!!) (b["split_expr_4"]!!)] b
  s₉ = c🇪⟦Clear.EVMState.sstore c.evm (c["slot"]!!) (c["split_expr_5"]!!)⟧

lemma block_8692170500034331446_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8692170500034331446_concrete_of_code s₀ s₉ →
  Spec A_block_8692170500034331446 s₀ s₉ := by
  unfold block_8692170500034331446_concrete_of_code A_block_8692170500034331446
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_8692170500034331446_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_8692170500034331446 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · rw [h]; simp [multifill_cons, multifill_nil, isOk_insert, isOk_setEvm]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_8692170500034331446_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_8692170500034331446 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_8692170500034331446_isOk hok h)

end

end L2InteropCommitmentTree.Common
