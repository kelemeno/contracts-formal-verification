import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes_calldata_ptr_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bytes_calldata_ptr (end_clear_sanitised_hrafn : Identifier) (start length pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes_calldata_ptr_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn start length pos} :
  Spec (abi_encode_bytes_calldata_ptr_concrete_of_code.1 end_clear_sanitised_hrafn start length pos) s₀ s₉ →
  Spec (A_abi_encode_bytes_calldata_ptr end_clear_sanitised_hrafn start length pos) s₀ s₉ := by
  unfold abi_encode_bytes_calldata_ptr_concrete_of_code A_abi_encode_bytes_calldata_ptr
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
