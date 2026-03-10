import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop := True

lemma mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_abs_of_concrete {s₀ s₉ : State} {dataSlot slot key} :
  Spec (mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_concrete_of_code.1 dataSlot slot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 dataSlot slot key) s₀ s₉ := by
  unfold A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
