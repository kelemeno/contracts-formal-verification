import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_array_bytes32_dyn
import generated.L1Nullifier.L1Nullifier.abi_encode_enum_TxStatus

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus (tail : Identifier) (headStart value0 value1 value2 value3 value4 value5 value6 : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus_concrete_of_code.1 tail headStart value0 value1 value2 value3 value4 value5 value6 s₀ s₉

lemma abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3 value4 value5 value6} :
  Spec (abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus_concrete_of_code.1 tail headStart value0 value1 value2 value3 value4 value5 value6) s₀ s₉ →
  Spec (A_abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus tail headStart value0 value1 value2 value3 value4 value5 value6) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_uint256_bytes32_uint256_uint256_uint16_array_bytes32_dyn_enum_TxStatus] using h

end

end generated.L1Nullifier.L1Nullifier
