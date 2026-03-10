import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_getSelector
import generated.L1Nullifier.L1Nullifier.Common.switch_7134055336228242222
import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData
import generated.L1Nullifier.L1Nullifier.fun_decodeLegacyFinalizeWithdrawalData
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_error_TokenNotLegacy
import generated.L1Nullifier.L1Nullifier.fun_decodeBaseTokenFinalizeWithdrawalData
import generated.L1Nullifier.L1Nullifier.fun_encodeBridgeMintData_17779
import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_array_bytes

import generated.L1Nullifier.L1Nullifier.fun_parseL2WithdrawalMessage_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_parseL2WithdrawalMessage (var_assetId var_transferData_1336_mpos : Identifier) (var_chainId var_l2ToL1message_1331_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_parseL2WithdrawalMessage_abs_of_concrete {s₀ s₉ : State} {var_assetId var_transferData_1336_mpos var_chainId var_l2ToL1message_1331_mpos} :
  Spec (fun_parseL2WithdrawalMessage_concrete_of_code.1 var_assetId var_transferData_1336_mpos var_chainId var_l2ToL1message_1331_mpos) s₀ s₉ →
  Spec (A_fun_parseL2WithdrawalMessage var_assetId var_transferData_1336_mpos var_chainId var_l2ToL1message_1331_mpos) s₀ s₉ := by
  unfold A_fun_parseL2WithdrawalMessage
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
