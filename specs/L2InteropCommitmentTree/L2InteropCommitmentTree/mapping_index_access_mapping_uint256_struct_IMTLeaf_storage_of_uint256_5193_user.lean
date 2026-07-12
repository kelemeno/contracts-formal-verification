import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop := mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193_concrete_of_code.1 dataSlot key s₀ s₉

lemma mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193 dataSlot key) s₀ s₉ := by
  intro h
  simpa [A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_5193] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
