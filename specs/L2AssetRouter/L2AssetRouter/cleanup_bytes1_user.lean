import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.cleanup_bytes1_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_cleanup_bytes1 (cleaned : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma cleanup_bytes1_abs_of_concrete {s₀ s₉ : State} {cleaned value} :
  Spec (cleanup_bytes1_concrete_of_code.1 cleaned value) s₀ s₉ →
  Spec (A_cleanup_bytes1 cleaned value) s₀ s₉ := by
  unfold cleanup_bytes1_concrete_of_code A_cleanup_bytes1
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
