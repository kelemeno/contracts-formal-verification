import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7714157185465443049_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Read and clear the low byte**, first half of the `LegState` write:

```
    let cleaned := 0; cleaned := 0
    let split_expr_0 := sload(slot)
    let split_expr_1 := not(255)
    let split_expr_2 := and(split_expr_0, split_expr_1)
```

`and(word, not(255))` keeps every byte of the packed slot EXCEPT the low one — so
the other fields sharing this slot survive the write that follows.  The dead
`cleaned := 0` pair is solc's zero-initialisation of a local it then never uses. -/
def A_block_7714157185465443049 (s₀ s₉ : State) : Prop :=
  let s₁ := s₀⟦"cleaned" ↦ 0⟧
  let s₂ := s₁⟦"split_expr_0" ↦ Clear.EVMState.sload s₀.evm (s₁["slot"]!!)⟧
  let s₃ := s₂⟦"split_expr_1" ↦ UInt256.lnot 255⟧
  s₉ = Clear.State.multifill ["split_expr_2"]
    [Fin.land (s₃["split_expr_0"]!!) (s₃["split_expr_1"]!!)] s₃

lemma block_7714157185465443049_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7714157185465443049_concrete_of_code s₀ s₉ →
  Spec A_block_7714157185465443049 s₀ s₉ := by
  unfold block_7714157185465443049_concrete_of_code A_block_7714157185465443049
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_7714157185465443049_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_7714157185465443049 s₀ s₉) : isOk s₉ := by
  rw [h]
  exact isOk_multifill (by simp only [isOk_insert]; exact hok)

lemma block_7714157185465443049_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_7714157185465443049 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_7714157185465443049_isOk hok h)

end

end AtomicFlowManager.Common
