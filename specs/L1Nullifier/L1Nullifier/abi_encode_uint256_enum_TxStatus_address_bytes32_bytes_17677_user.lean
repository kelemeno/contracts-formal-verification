import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677 (tail : Identifier) (headStart value0 value2 value3 value4 : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677_concrete_of_code.1 tail headStart value0 value2 value3 value4 s₀ s₉

lemma abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value2 value3 value4} :
  Spec (abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677_concrete_of_code.1 tail headStart value0 value2 value3 value4) s₀ s₉ →
  Spec (A_abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677 tail headStart value0 value2 value3 value4) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_uint256_enum_TxStatus_address_bytes32_bytes_17677] using h

end

end generated.L1Nullifier.L1Nullifier
