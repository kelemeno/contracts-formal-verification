import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.abi_decode_uint256_11715_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_decode_uint256_11715 (value : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_uint256_11715_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint256_11715_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_uint256_11715 value ) s₀ s₉ := by
  unfold abi_decode_uint256_11715_concrete_of_code A_abi_decode_uint256_11715
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
