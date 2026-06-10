import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677

import generated.L1Nullifier.L1Nullifier.Common.block_537517597180609273_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_537517597180609273 (s₀ s₉ : State) : Prop := block_537517597180609273_concrete_of_code.1 s₀ s₉

lemma block_537517597180609273_abs_of_concrete {s₀ s₉ : State} :
  Spec block_537517597180609273_concrete_of_code s₀ s₉ →
  Spec A_block_537517597180609273 s₀ s₉ := by
  intro h
  simpa [A_block_537517597180609273] using h

end

end L1Nullifier.Common
