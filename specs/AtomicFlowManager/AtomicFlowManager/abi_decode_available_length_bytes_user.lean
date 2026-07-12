import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_4148053531410514966
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2351523785055460648
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5048230786942213600
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5064767104898712986

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_available_length_bytes_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_abi_decode_available_length_bytes (array : Identifier) (src length end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_available_length_bytes_concrete_of_code.1 array src length end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_available_length_bytes_abs_of_concrete {s₀ s₉ : State} {array src length end_clear_sanitised_hrafn} :
  Spec (abi_decode_available_length_bytes_concrete_of_code.1 array src length end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_available_length_bytes array src length end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_available_length_bytes] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
