import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_bool_to_bool_17751_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_update_storage_value_offset_bool_to_bool_17751  (slot : Literal) (s₀ s₉ : State) : Prop := update_storage_value_offset_bool_to_bool_17751_concrete_of_code.1  slot s₀ s₉

lemma update_storage_value_offset_bool_to_bool_17751_abs_of_concrete {s₀ s₉ : State} { slot} :
  Spec (update_storage_value_offset_bool_to_bool_17751_concrete_of_code.1  slot) s₀ s₉ →
  Spec (A_update_storage_value_offset_bool_to_bool_17751  slot) s₀ s₉ := by
  intro h
  simpa [A_update_storage_value_offset_bool_to_bool_17751] using h

end

end generated.L1Nullifier.L1Nullifier
