import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_7928665324398554026
import generated.L1Nullifier.L1Nullifier.Common.if_6747681429752853338
import generated.L1Nullifier.L1Nullifier.Common.if_5631566510356250141

import generated.L1Nullifier.L1Nullifier.abi_decode_bytes_calldata_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode_bytes_calldata (arrayPos length : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_calldata_abs_of_concrete {s₀ s₉ : State} {arrayPos length offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_calldata_concrete_of_code.1 arrayPos length offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes_calldata arrayPos length offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_calldata_concrete_of_code A_abi_decode_bytes_calldata
  sorry

end

end generated.L1Nullifier.L1Nullifier
