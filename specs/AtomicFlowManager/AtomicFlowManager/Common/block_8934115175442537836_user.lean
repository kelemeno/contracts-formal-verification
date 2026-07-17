import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8934115175442537836_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_8934115175442537836 (s₀ s₉ : State) : Prop := sorry

lemma block_8934115175442537836_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8934115175442537836_concrete_of_code s₀ s₉ →
  Spec A_block_8934115175442537836 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
