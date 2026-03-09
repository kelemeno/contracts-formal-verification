import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_address_address (tail : Identifier) (headStart value0 value1 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_address_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1} :
  Spec (abi_encode_address_address_concrete_of_code.1 tail headStart value0 value1) s₀ s₉ →
  Spec (A_abi_encode_address_address tail headStart value0 value1) s₀ s₉ := by
  unfold abi_encode_address_address_concrete_of_code A_abi_encode_address_address
  sorry

end

end generated.L1AssetRouter.L1AssetRouter
