import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_7701508804347977427
import generated.L1Nullifier.L1Nullifier.abi_encode_address_bytes32_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes
import generated.L1Nullifier.L1Nullifier.abi_encode_uint256
import generated.L1Nullifier.L1Nullifier.Common.if_9097063384830582942
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_4144600630884638834
import generated.L1Nullifier.L1Nullifier.abi_decode_address_fromMemory
import generated.L1Nullifier.L1Nullifier.Common.if_5909860842735680253
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_address
import generated.L1Nullifier.L1Nullifier.fun_decodeBridgeBurnData
import generated.L1Nullifier.L1Nullifier.abi_encode_address_address_uint256

import generated.L1Nullifier.L1Nullifier.Common.switch_5752467948547937291_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_5752467948547937291 (s₀ s₉ : State) : Prop := sorry

lemma switch_5752467948547937291_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5752467948547937291_concrete_of_code s₀ s₉ →
  Spec A_switch_5752467948547937291 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
