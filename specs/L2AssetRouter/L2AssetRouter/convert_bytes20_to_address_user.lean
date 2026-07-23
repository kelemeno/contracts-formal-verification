import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.convert_bytes20_to_address_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_convert_bytes20_to_address (converted : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := convert_bytes20_to_address_concrete_of_code.1 converted value s₀ s₉

lemma convert_bytes20_to_address_abs_of_concrete {s₀ s₉ : State} {converted value} :
  Spec (convert_bytes20_to_address_concrete_of_code.1 converted value) s₀ s₉ →
  Spec (A_convert_bytes20_to_address converted value) s₀ s₉ := by
  intro h
  simpa [A_convert_bytes20_to_address] using h

end

end generated.L2AssetRouter.L2AssetRouter
