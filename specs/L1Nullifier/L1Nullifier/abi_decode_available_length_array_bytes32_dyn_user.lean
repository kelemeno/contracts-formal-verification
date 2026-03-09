import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_4148053531410514966
import generated.L1Nullifier.L1Nullifier.panic_error_0x41
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.Common.if_4884626539333129882
import generated.L1Nullifier.L1Nullifier.Common.for_6136861723173755809

import generated.L1Nullifier.L1Nullifier.abi_decode_available_length_array_bytes32_dyn_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_abi_decode_available_length_array_bytes32_dyn (array : Identifier) (offset length end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_available_length_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {array offset length end_clear_sanitised_hrafn} :
  Spec (abi_decode_available_length_array_bytes32_dyn_concrete_of_code.1 array offset length end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_available_length_array_bytes32_dyn array offset length end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_available_length_array_bytes32_dyn_concrete_of_code A_abi_decode_available_length_array_bytes32_dyn
  sorry

end

end generated.L1Nullifier.L1Nullifier
