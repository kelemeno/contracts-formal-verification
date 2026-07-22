import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.abi_encode_address_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_address (tail : Identifier) (value0 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_address_abs_of_concrete {s₀ s₉ : State} {tail value0} :
  Spec (abi_encode_address_concrete_of_code.1 tail value0) s₀ s₉ →
  Spec (A_abi_encode_address tail value0) s₀ s₉ := by
  unfold abi_encode_address_concrete_of_code A_abi_encode_address
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
