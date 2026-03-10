import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_address_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_read_from_storage_split_offset_address (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := True

lemma read_from_storage_split_offset_address_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_split_offset_address_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_address value slot) s₀ s₉ := by
  unfold A_read_from_storage_split_offset_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
