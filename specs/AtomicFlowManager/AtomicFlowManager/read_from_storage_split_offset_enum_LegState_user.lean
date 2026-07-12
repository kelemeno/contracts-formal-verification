import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_read_from_storage_split_offset_enum_LegState (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := read_from_storage_split_offset_enum_LegState_concrete_of_code.1 value slot s₀ s₉

lemma read_from_storage_split_offset_enum_LegState_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_split_offset_enum_LegState_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_enum_LegState value slot) s₀ s₉ := by
  intro h
  simpa [A_read_from_storage_split_offset_enum_LegState] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
