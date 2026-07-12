import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_l2MessageToLog
import generated.AtomicFlowManager.AtomicFlowManager.fun_getLeafHashFromLog
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.fun_getProofData

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6769537869963839068_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_6769537869963839068 (s₀ s₉ : State) : Prop := block_6769537869963839068_concrete_of_code.1 s₀ s₉

lemma block_6769537869963839068_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6769537869963839068_concrete_of_code s₀ s₉ →
  Spec A_block_6769537869963839068 s₀ s₉ := by
  intro h
  simpa [A_block_6769537869963839068] using h

end

end AtomicFlowManager.Common
