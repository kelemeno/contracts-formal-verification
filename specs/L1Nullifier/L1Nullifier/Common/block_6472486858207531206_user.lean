import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_enum_TxStatus_address_bytes32_bytes

import generated.L1Nullifier.L1Nullifier.Common.block_6472486858207531206_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_6472486858207531206 (s₀ s₉ : State) : Prop := block_6472486858207531206_concrete_of_code.1 s₀ s₉

lemma block_6472486858207531206_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6472486858207531206_concrete_of_code s₀ s₉ →
  Spec A_block_6472486858207531206 s₀ s₉ := by
  intro h
  simpa [A_block_6472486858207531206] using h

end

end L1Nullifier.Common
