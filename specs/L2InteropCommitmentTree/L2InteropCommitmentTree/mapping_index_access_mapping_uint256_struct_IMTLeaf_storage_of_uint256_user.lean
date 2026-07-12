import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256 (dataSlot : Identifier)  (s₀ s₉ : State) : Prop := mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_concrete_of_code.1 dataSlot s₀ s₉

lemma mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_abs_of_concrete {s₀ s₉ : State} {dataSlot } :
  Spec (mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256_concrete_of_code.1 dataSlot ) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256 dataSlot ) s₀ s₉ := by
  intro h
  simpa [A_mapping_index_access_mapping_uint256_struct_IMTLeaf_storage_of_uint256] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
