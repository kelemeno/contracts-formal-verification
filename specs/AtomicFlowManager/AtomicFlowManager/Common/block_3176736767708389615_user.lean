import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3176736767708389615_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3176736767708389615 (s₀ s₉ : State) : Prop := sorry

lemma block_3176736767708389615_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3176736767708389615_concrete_of_code s₀ s₉ →
  Spec A_block_3176736767708389615 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
