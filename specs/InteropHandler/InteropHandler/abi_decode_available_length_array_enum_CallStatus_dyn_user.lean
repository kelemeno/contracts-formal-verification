import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_3074887667850422543
import generated.InteropHandler.InteropHandler.array_allocation_size_array_bytes32_dyn
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_6636810931393710079
import generated.InteropHandler.InteropHandler.Common.if_4884626539333129882
import generated.InteropHandler.InteropHandler.Common.for_7496197131413067314

import generated.InteropHandler.InteropHandler.abi_decode_available_length_array_enum_CallStatus_dyn_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_abi_decode_available_length_array_enum_CallStatus_dyn (array : Identifier) (offset length end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_available_length_array_enum_CallStatus_dyn_abs_of_concrete {s₀ s₉ : State} {array offset length end_clear_sanitised_hrafn} :
  Spec (abi_decode_available_length_array_enum_CallStatus_dyn_concrete_of_code.1 array offset length end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_available_length_array_enum_CallStatus_dyn array offset length end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_available_length_array_enum_CallStatus_dyn_concrete_of_code A_abi_decode_available_length_array_enum_CallStatus_dyn
  sorry

end

end generated.InteropHandler.InteropHandler
