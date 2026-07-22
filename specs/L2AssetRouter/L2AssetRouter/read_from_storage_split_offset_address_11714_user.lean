import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.read_from_storage_split_offset_address_11714_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_read_from_storage_split_offset_address_11714 (value : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma read_from_storage_split_offset_address_11714_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (read_from_storage_split_offset_address_11714_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_address_11714 value ) s₀ s₉ := by
  unfold read_from_storage_split_offset_address_11714_concrete_of_code A_read_from_storage_split_offset_address_11714
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
