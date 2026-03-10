import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_7322987041177811756_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

-- The overflow condition for finalize_allocation:
-- `or(gt(newFreePtr, 18446744073709551615), lt(newFreePtr, memPtr))`
def finalize_allocation_overflow (s : State) : Prop :=
  s["newFreePtr"]!! > 18446744073709551615 ∨ s["newFreePtr"]!! < s["memPtr"]!!

-- When no overflow, the if-block passes through unchanged.
-- When overflow, the block reverts (EVM-level, VarStore unchanged).
def A_if_7322987041177811756 (s₀ s₉ : State) : Prop :=
  ¬ finalize_allocation_overflow s₀ → s₉ = s₀

lemma if_7322987041177811756_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7322987041177811756_concrete_of_code s₀ s₉ →
  Spec A_if_7322987041177811756 s₀ s₉ := by
  unfold A_if_7322987041177811756
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete hnooverflow
  -- The concrete spec says: if overflow condition is 0, then s₉ = s₀.
  -- Since ¬ finalize_allocation_overflow, the condition evaluates to 0.
  sorry

end

end L1AssetRouter.Common
