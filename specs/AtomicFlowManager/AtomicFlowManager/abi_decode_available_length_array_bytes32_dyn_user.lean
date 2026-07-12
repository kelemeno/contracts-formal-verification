import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3502045432915694067
import generated.AtomicFlowManager.AtomicFlowManager.array_allocation_size_array_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6636810931393710079
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_4884626539333129882
import generated.AtomicFlowManager.AtomicFlowManager.Common.for_6136861723173755809

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_available_length_array_bytes32_dyn_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_abi_decode_available_length_array_bytes32_dyn (array : Identifier) (offset length end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_available_length_array_bytes32_dyn_concrete_of_code.1 array offset length end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_available_length_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {array offset length end_clear_sanitised_hrafn} :
  Spec (abi_decode_available_length_array_bytes32_dyn_concrete_of_code.1 array offset length end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_available_length_array_bytes32_dyn array offset length end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_available_length_array_bytes32_dyn] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
