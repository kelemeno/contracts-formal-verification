import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6283262372819999209_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_6283262372819999209 (s₀ s₉ : State) : Prop := sorry

lemma block_6283262372819999209_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6283262372819999209_concrete_of_code s₀ s₉ →
  Spec A_block_6283262372819999209 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
