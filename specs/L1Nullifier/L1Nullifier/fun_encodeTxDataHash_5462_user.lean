import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_7230237767825797901
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.abi_decode_address_fromMemory
import generated.L1Nullifier.L1Nullifier.fun_decodeBridgeBurnData

import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash_5462_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_encodeTxDataHash_5462 (var_txDataHash : Identifier) (var_encodingVersion var_originalCaller var_assetId var_nativeTokenVault var_transferData_5382_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_encodeTxDataHash_5462_abs_of_concrete {s₀ s₉ : State} {var_txDataHash var_encodingVersion var_originalCaller var_assetId var_nativeTokenVault var_transferData_5382_mpos} :
  Spec (fun_encodeTxDataHash_5462_concrete_of_code.1 var_txDataHash var_encodingVersion var_originalCaller var_assetId var_nativeTokenVault var_transferData_5382_mpos) s₀ s₉ →
  Spec (A_fun_encodeTxDataHash_5462 var_txDataHash var_encodingVersion var_originalCaller var_assetId var_nativeTokenVault var_transferData_5382_mpos) s₀ s₉ := by
  unfold fun_encodeTxDataHash_5462_concrete_of_code A_fun_encodeTxDataHash_5462
  sorry

end

end generated.L1Nullifier.L1Nullifier
