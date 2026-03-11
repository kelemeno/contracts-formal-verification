import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_9164576800569104854
import generated.L1Nullifier.L1Nullifier.abi_encode_address_bytes32_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes
import generated.L1Nullifier.L1Nullifier.abi_encode_uint256
import generated.L1Nullifier.L1Nullifier.Common.if_9097063384830582942
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_3708168804682849505
import generated.L1Nullifier.L1Nullifier.abi_decode_address_fromMemory
import generated.L1Nullifier.L1Nullifier.fun_encodeNTVAssetId
import generated.L1Nullifier.L1Nullifier.Common.if_415909480136577781
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_address
import generated.L1Nullifier.L1Nullifier.fun_decodeBridgeBurnData
import generated.L1Nullifier.L1Nullifier.abi_encode_address_address_uint256

import generated.L1Nullifier.L1Nullifier.Common.switch_1586331052463743141_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_1586331052463743141 (s₀ s₉ : State) : Prop :=
  switch_1586331052463743141_concrete_of_code.1 s₀ s₉

lemma switch_1586331052463743141_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1586331052463743141_concrete_of_code s₀ s₉ →
  Spec A_switch_1586331052463743141 s₀ s₉ := by
  intro h
  simpa [A_switch_1586331052463743141] using h

end

end L1Nullifier.Common
