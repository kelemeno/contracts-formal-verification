import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.update_storage_value_offset_bool_to_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_update_storage_value_offset_bool_to_bool   (s₀ s₉ : State) : Prop := True

lemma update_storage_value_offset_bool_to_bool_abs_of_concrete {s₀ s₉ : State} :
  Spec (update_storage_value_offset_bool_to_bool_concrete_of_code.1 ) s₀ s₉ →
  Spec (A_update_storage_value_offset_bool_to_bool ) s₀ s₉ := by
  unfold A_update_storage_value_offset_bool_to_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
