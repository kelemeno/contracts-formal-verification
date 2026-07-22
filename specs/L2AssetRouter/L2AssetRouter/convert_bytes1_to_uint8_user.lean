import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.convert_bytes1_to_uint8_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_convert_bytes1_to_uint8 (converted : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma convert_bytes1_to_uint8_abs_of_concrete {s₀ s₉ : State} {converted value} :
  Spec (convert_bytes1_to_uint8_concrete_of_code.1 converted value) s₀ s₉ →
  Spec (A_convert_bytes1_to_uint8 converted value) s₀ s₉ := by
  unfold convert_bytes1_to_uint8_concrete_of_code A_convert_bytes1_to_uint8
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
