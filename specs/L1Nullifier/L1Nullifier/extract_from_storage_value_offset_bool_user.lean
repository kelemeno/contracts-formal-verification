import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.extract_from_storage_value_offset_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_extract_from_storage_value_offset_bool (value : Identifier) (slot_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma extract_from_storage_value_offset_bool_abs_of_concrete {s₀ s₉ : State} {value slot_value} :
  Spec (extract_from_storage_value_offset_bool_concrete_of_code.1 value slot_value) s₀ s₉ →
  Spec (A_extract_from_storage_value_offset_bool value slot_value) s₀ s₉ := by
  unfold extract_from_storage_value_offset_bool_concrete_of_code A_extract_from_storage_value_offset_bool
  sorry

end

end generated.L1Nullifier.L1Nullifier
