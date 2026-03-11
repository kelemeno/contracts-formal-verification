import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes

import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_encodeTxDataHash (var_txDataHash : Identifier) (var_originalCaller var_assetId var_nativeTokenVault var_transferData_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_encodeTxDataHash_concrete_of_code.1 var_txDataHash var_originalCaller var_assetId var_nativeTokenVault var_transferData_mpos s₀ s₉

lemma fun_encodeTxDataHash_abs_of_concrete {s₀ s₉ : State} {var_txDataHash var_originalCaller var_assetId var_nativeTokenVault var_transferData_mpos} :
  Spec (fun_encodeTxDataHash_concrete_of_code.1 var_txDataHash var_originalCaller var_assetId var_nativeTokenVault var_transferData_mpos) s₀ s₉ →
  Spec (A_fun_encodeTxDataHash var_txDataHash var_originalCaller var_assetId var_nativeTokenVault var_transferData_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_encodeTxDataHash] using h

end

end generated.L1Nullifier.L1Nullifier
