import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_4669985319712420221
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata_7928_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_calldata_array_index_access_bytes32_dyn_calldata_7928 (addr : Identifier) (base_ref length : Literal) (s₀ s₉ : State) : Prop := calldata_array_index_access_bytes32_dyn_calldata_7928_concrete_of_code.1 addr base_ref length s₀ s₉

lemma calldata_array_index_access_bytes32_dyn_calldata_7928_abs_of_concrete {s₀ s₉ : State} {addr base_ref length} :
  Spec (calldata_array_index_access_bytes32_dyn_calldata_7928_concrete_of_code.1 addr base_ref length) s₀ s₉ →
  Spec (A_calldata_array_index_access_bytes32_dyn_calldata_7928 addr base_ref length) s₀ s₉ := by
  unfold calldata_array_index_access_bytes32_dyn_calldata_7928_concrete_of_code A_calldata_array_index_access_bytes32_dyn_calldata_7928
  intro h
  simpa [A_calldata_array_index_access_bytes32_dyn_calldata_7928] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
