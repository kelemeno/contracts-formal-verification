import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory
import generated.L1Nullifier.L1Nullifier.Common.switch_2352977164347510911

import generated.L1Nullifier.L1Nullifier.fun_isLegacyTxDataHash_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_isLegacyTxDataHash (var_isLegacyTxDataHash : Identifier) (var_depositSender var_assetId var__transferData_mpos var_expectedTxDataHash : Literal) (s₀ s₉ : State) : Prop :=
  fun_isLegacyTxDataHash_concrete_of_code.1 var_isLegacyTxDataHash var_depositSender var_assetId var__transferData_mpos var_expectedTxDataHash s₀ s₉

lemma fun_isLegacyTxDataHash_abs_of_concrete {s₀ s₉ : State} {var_isLegacyTxDataHash var_depositSender var_assetId var__transferData_mpos var_expectedTxDataHash} :
  Spec (fun_isLegacyTxDataHash_concrete_of_code.1 var_isLegacyTxDataHash var_depositSender var_assetId var__transferData_mpos var_expectedTxDataHash) s₀ s₉ →
  Spec (A_fun_isLegacyTxDataHash var_isLegacyTxDataHash var_depositSender var_assetId var__transferData_mpos var_expectedTxDataHash) s₀ s₉ := by
  intro h
  simpa [A_fun_isLegacyTxDataHash] using h

end

end generated.L1Nullifier.L1Nullifier
