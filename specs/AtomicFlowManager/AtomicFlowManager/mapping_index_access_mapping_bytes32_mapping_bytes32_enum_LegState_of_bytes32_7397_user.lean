import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop := mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397_concrete_of_code.1 dataSlot key s₀ s₉

lemma mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397 dataSlot key) s₀ s₉ := by
  intro h
  simpa [A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7397] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
