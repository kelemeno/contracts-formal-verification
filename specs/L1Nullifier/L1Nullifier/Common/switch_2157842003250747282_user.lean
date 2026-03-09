import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_530758481503891896
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes4
import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData
import generated.L1Nullifier.L1Nullifier.fun_decodeLegacyFinalizeWithdrawalData
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.abi_encode_address
import generated.L1Nullifier.L1Nullifier.Common.if_7069222774777857031
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_7504476991299295747
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory
import generated.L1Nullifier.L1Nullifier.fun_encodeNTVAssetId
import generated.L1Nullifier.L1Nullifier.require_helper_error_TokenNotLegacy

import generated.L1Nullifier.L1Nullifier.Common.switch_2157842003250747282_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_2157842003250747282 (s₀ s₉ : State) : Prop := sorry

lemma switch_2157842003250747282_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2157842003250747282_concrete_of_code s₀ s₉ →
  Spec A_switch_2157842003250747282 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
