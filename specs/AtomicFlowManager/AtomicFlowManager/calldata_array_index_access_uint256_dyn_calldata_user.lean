import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6945705467323769142
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_calldata_array_index_access_uint256_dyn_calldata (addr : Identifier) (base_ref length index : Literal) (s₀ s₉ : State) : Prop := calldata_array_index_access_uint256_dyn_calldata_concrete_of_code.1 addr base_ref length index s₀ s₉

lemma calldata_array_index_access_uint256_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {addr base_ref length index} :
  Spec (calldata_array_index_access_uint256_dyn_calldata_concrete_of_code.1 addr base_ref length index) s₀ s₉ →
  Spec (A_calldata_array_index_access_uint256_dyn_calldata addr base_ref length index) s₀ s₉ := by
  intro h
  simpa [A_calldata_array_index_access_uint256_dyn_calldata] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
