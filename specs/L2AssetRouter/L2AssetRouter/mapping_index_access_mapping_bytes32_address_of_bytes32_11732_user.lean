import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.mapping_index_access_mapping_bytes32_address_of_bytes32_11732_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_bytes32_address_of_bytes32_11732 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop := mapping_index_access_mapping_bytes32_address_of_bytes32_11732_concrete_of_code.1 dataSlot key s₀ s₉

lemma mapping_index_access_mapping_bytes32_address_of_bytes32_11732_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_bytes32_address_of_bytes32_11732_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_bytes32_address_of_bytes32_11732 dataSlot key) s₀ s₉ := by
  intro h
  simpa [A_mapping_index_access_mapping_bytes32_address_of_bytes32_11732] using h

end

end generated.L2AssetRouter.L2AssetRouter
