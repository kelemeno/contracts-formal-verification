import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_decode_available_length_array_bytes32_dyn

import generated.L1Nullifier.L1Nullifier.abi_decode_array_bytes32_dyn_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_abi_decode_array_bytes32_dyn (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_array_bytes32_dyn_concrete_of_code.1 array offset end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_array_bytes32_dyn_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_array_bytes32_dyn array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_array_bytes32_dyn] using h

end

end generated.L1Nullifier.L1Nullifier
