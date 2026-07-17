import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7714157185465443049
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_9060002175079746718

import generated.AtomicFlowManager.AtomicFlowManager.update_storage_value_offset_enum_LegState_to_enum_LegState_7852_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_update_storage_value_offset_enum_LegState_to_enum_LegState_7852  (slot : Literal) (s₀ s₉ : State) : Prop := sorry

lemma update_storage_value_offset_enum_LegState_to_enum_LegState_7852_abs_of_concrete {s₀ s₉ : State} { slot} :
  Spec (update_storage_value_offset_enum_LegState_to_enum_LegState_7852_concrete_of_code.1  slot) s₀ s₉ →
  Spec (A_update_storage_value_offset_enum_LegState_to_enum_LegState_7852  slot) s₀ s₉ := by
  unfold update_storage_value_offset_enum_LegState_to_enum_LegState_7852_concrete_of_code A_update_storage_value_offset_enum_LegState_to_enum_LegState_7852
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager
