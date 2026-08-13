import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6033096439800527865_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The wraparound flag**: `split_expr_4 := lt(newFreePtr, memPtr)`.

Set when the rounded allocation made the free pointer go BACKWARDS, i.e. the addition
overflowed.  Checked alongside the ceiling flag. -/
def A_block_6033096439800527865 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_4" ↦ if s₀["newFreePtr"]!! < s₀["memPtr"]!! then 1 else 0⟧

lemma block_6033096439800527865_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6033096439800527865_concrete_of_code s₀ s₉ →
  Spec A_block_6033096439800527865 s₀ s₉ := by
  unfold block_6033096439800527865_concrete_of_code A_block_6033096439800527865
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_6033096439800527865_isOk {s₀ s₉ : State} (hok : isOk s₀) (h : A_block_6033096439800527865 s₀ s₉) : isOk s₉ := by
  rw [h]; simp only [isOk_insert]; exact hok

lemma block_6033096439800527865_not_break {s₀ s₉ : State} (hok : isOk s₀) (h : A_block_6033096439800527865 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_6033096439800527865_isOk hok h)

end

end AtomicFlowManager.Common
