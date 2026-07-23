import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.update_storage_value_offset_uint256_to_uint256_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_update_storage_value_offset_uint256_to_uint256  (value : Literal) (s₀ s₉ : State) : Prop := update_storage_value_offset_uint256_to_uint256_concrete_of_code.1 value s₀ s₉

lemma update_storage_value_offset_uint256_to_uint256_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (update_storage_value_offset_uint256_to_uint256_concrete_of_code.1  value) s₀ s₉ →
  Spec (A_update_storage_value_offset_uint256_to_uint256  value) s₀ s₉ := by
  intro h
  simpa [A_update_storage_value_offset_uint256_to_uint256] using h

end

end generated.L2AssetRouter.L2AssetRouter
