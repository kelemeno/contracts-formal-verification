import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_3489657594510812776_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

-- The overflow condition for finalize_allocation (new preprocessor split form):
-- `or(gt(newFreePtr, 18446744073709551615), lt(newFreePtr, memPtr))`
-- stored in split_expr_3 = gt(newFreePtr, MAX) and split_expr_4 = lt(newFreePtr, memPtr)
def finalize_allocation_overflow (s : State) : Prop :=
  s["split_expr_3"]!! ≠ 0 ∨ s["split_expr_4"]!! ≠ 0

-- When no overflow, the if-block passes through unchanged.
-- When overflow, the block reverts (EVM-level, VarStore unchanged).
def A_if_3489657594510812776 (s₀ s₉ : State) : Prop :=
  ¬ finalize_allocation_overflow s₀ → s₉ = s₀

lemma if_3489657594510812776_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3489657594510812776_concrete_of_code s₀ s₉ →
  Spec A_if_3489657594510812776 s₀ s₉ := by
  unfold A_if_3489657594510812776
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete hnooverflow
  sorry

end

end L1AssetRouter.Common
