import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop := sorry

lemma mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199 dataSlot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199_concrete_of_code A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5199
  sorry

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
