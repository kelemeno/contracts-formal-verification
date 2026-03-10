import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop := True

lemma mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729 dataSlot key) s₀ s₉ := by
  unfold A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
