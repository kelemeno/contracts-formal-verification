import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_enum_TxStatus
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_abi_encode_uint256_enum_TxStatus_address_bytes32_bytes (tail : Identifier) (headStart value0 value1 value2 value3 value4 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3 value4} :
  Spec (abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_concrete_of_code.1 tail headStart value0 value1 value2 value3 value4) s₀ s₉ →
  Spec (A_abi_encode_uint256_enum_TxStatus_address_bytes32_bytes tail headStart value0 value1 value2 value3 value4) s₀ s₉ := by
  unfold abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_concrete_of_code A_abi_encode_uint256_enum_TxStatus_address_bytes32_bytes
  sorry

end

end generated.L1Nullifier.L1Nullifier
