import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_3074887667850422543
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_array_bytes32_dyn
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_6636810931393710079
import generated.L2InteropHandler.L2InteropHandler.Common.if_4884626539333129882
import generated.L2InteropHandler.L2InteropHandler.Common.for_7496197131413067314

import generated.L2InteropHandler.L2InteropHandler.abi_decode_available_length_array_enum_CallStatus_dyn_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_decode_available_length_array_enum_CallStatus_dyn (array : Identifier) (offset length end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_available_length_array_enum_CallStatus_dyn_concrete_of_code.1 array offset length end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_available_length_array_enum_CallStatus_dyn_abs_of_concrete {s₀ s₉ : State} {array offset length end_clear_sanitised_hrafn} :
  Spec (abi_decode_available_length_array_enum_CallStatus_dyn_concrete_of_code.1 array offset length end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_available_length_array_enum_CallStatus_dyn array offset length end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_available_length_array_enum_CallStatus_dyn] using h

end

end generated.L2InteropHandler.L2InteropHandler
