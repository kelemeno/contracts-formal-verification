import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6743186873342481897
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5731116343986243113
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1209118431116190868
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6747681429752853338
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8835011984658778953

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_access_calldata_tail_array_bytes32_dyn_calldata (addr length : Identifier) (base_ref ptr_to_tail : Literal) (s₀ s₉ : State) : Prop := access_calldata_tail_array_bytes32_dyn_calldata_concrete_of_code.1 addr length base_ref ptr_to_tail s₀ s₉

lemma access_calldata_tail_array_bytes32_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {addr length base_ref ptr_to_tail} :
  Spec (access_calldata_tail_array_bytes32_dyn_calldata_concrete_of_code.1 addr length base_ref ptr_to_tail) s₀ s₉ →
  Spec (A_access_calldata_tail_array_bytes32_dyn_calldata addr length base_ref ptr_to_tail) s₀ s₉ := by
  unfold access_calldata_tail_array_bytes32_dyn_calldata_concrete_of_code A_access_calldata_tail_array_bytes32_dyn_calldata
  intro h
  simpa [A_access_calldata_tail_array_bytes32_dyn_calldata] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
