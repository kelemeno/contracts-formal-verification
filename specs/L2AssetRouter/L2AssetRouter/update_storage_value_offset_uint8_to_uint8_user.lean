import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.update_storage_value_offset_uint8_to_uint8_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_update_storage_value_offset_uint8_to_uint8   (s₀ s₉ : State) : Prop := update_storage_value_offset_uint8_to_uint8_concrete_of_code.1 s₀ s₉

lemma update_storage_value_offset_uint8_to_uint8_abs_of_concrete {s₀ s₉ : State}  :
  Spec (update_storage_value_offset_uint8_to_uint8_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_update_storage_value_offset_uint8_to_uint8  ) s₀ s₉ := by
  intro h
  simpa [A_update_storage_value_offset_uint8_to_uint8] using h

end

end generated.L2AssetRouter.L2AssetRouter
