import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.constant_L2_INTEROP_HANDLER_ADDR_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_constant_L2_INTEROP_HANDLER_ADDR (ret : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma constant_L2_INTEROP_HANDLER_ADDR_abs_of_concrete {s₀ s₉ : State} {ret } :
  Spec (constant_L2_INTEROP_HANDLER_ADDR_concrete_of_code.1 ret ) s₀ s₉ →
  Spec (A_constant_L2_INTEROP_HANDLER_ADDR ret ) s₀ s₉ := by
  unfold constant_L2_INTEROP_HANDLER_ADDR_concrete_of_code A_constant_L2_INTEROP_HANDLER_ADDR
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
