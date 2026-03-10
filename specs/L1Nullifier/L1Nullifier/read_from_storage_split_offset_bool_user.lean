import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_read_from_storage_split_offset_bool (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := True

lemma read_from_storage_split_offset_bool_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_split_offset_bool_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_bool value slot) s₀ s₉ := by
  unfold A_read_from_storage_split_offset_bool
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
