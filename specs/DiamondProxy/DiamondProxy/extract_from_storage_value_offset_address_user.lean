import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.extract_from_storage_value_offset_address_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_extract_from_storage_value_offset_address (value : Identifier) (slot_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma extract_from_storage_value_offset_address_abs_of_concrete {s₀ s₉ : State} {value slot_value} :
  Spec (extract_from_storage_value_offset_address_concrete_of_code.1 value slot_value) s₀ s₉ →
  Spec (A_extract_from_storage_value_offset_address value slot_value) s₀ s₉ := by
  unfold extract_from_storage_value_offset_address_concrete_of_code A_extract_from_storage_value_offset_address
  sorry

end

end generated.DiamondProxy.DiamondProxy
