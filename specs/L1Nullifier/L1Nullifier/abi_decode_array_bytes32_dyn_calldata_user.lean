import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_6747681429752853338

import generated.L1Nullifier.L1Nullifier.abi_decode_array_bytes32_dyn_calldata_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode_array_bytes32_dyn_calldata (arrayPos length : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_array_bytes32_dyn_calldata_concrete_of_code.1 arrayPos length offset end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_array_bytes32_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {arrayPos length offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_array_bytes32_dyn_calldata_concrete_of_code.1 arrayPos length offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_array_bytes32_dyn_calldata arrayPos length offset end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_array_bytes32_dyn_calldata] using h

end

end generated.L1Nullifier.L1Nullifier
