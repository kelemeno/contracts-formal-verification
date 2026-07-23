import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.shift_right_uint256_uint8
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1406667599965785415_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_1406667599965785415 (s₀ s₉ : State) : Prop := block_1406667599965785415_concrete_of_code.1 s₀ s₉

lemma block_1406667599965785415_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1406667599965785415_concrete_of_code s₀ s₉ →
  Spec A_block_1406667599965785415 s₀ s₉ := by
  intro h
  simpa [A_block_1406667599965785415] using h

end

end AtomicFlowManager.Common
