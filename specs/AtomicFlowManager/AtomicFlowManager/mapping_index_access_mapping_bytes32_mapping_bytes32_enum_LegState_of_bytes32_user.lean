import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32 (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop := mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_concrete_of_code.1 dataSlot slot key s₀ s₉

lemma mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_abs_of_concrete {s₀ s₉ : State} {dataSlot slot key} :
  Spec (mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_concrete_of_code.1 dataSlot slot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32 dataSlot slot key) s₀ s₉ := by
  intro h
  simpa [A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
