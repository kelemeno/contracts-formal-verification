import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.array_allocation_size_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.abi_decode_available_length_bytes_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_abi_decode_available_length_bytes (array : Identifier) (src length end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_available_length_bytes_concrete_of_code.1 array src length end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_available_length_bytes_abs_of_concrete {s₀ s₉ : State} {array src length end_clear_sanitised_hrafn} :
  Spec (abi_decode_available_length_bytes_concrete_of_code.1 array src length end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_available_length_bytes array src length end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_available_length_bytes] using h

end

end generated.L1Nullifier.L1Nullifier
