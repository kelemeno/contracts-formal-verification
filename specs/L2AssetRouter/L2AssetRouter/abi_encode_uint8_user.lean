import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.abi_encode_uint8_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint8 (tail : Identifier) (headStart : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_uint8_abs_of_concrete {s₀ s₉ : State} {tail headStart} :
  Spec (abi_encode_uint8_concrete_of_code.1 tail headStart) s₀ s₉ →
  Spec (A_abi_encode_uint8 tail headStart) s₀ s₉ := by
  unfold abi_encode_uint8_concrete_of_code A_abi_encode_uint8
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
