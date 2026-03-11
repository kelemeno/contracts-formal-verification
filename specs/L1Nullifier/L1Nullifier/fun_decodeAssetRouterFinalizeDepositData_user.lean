import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_2095837721993293218
import generated.L1Nullifier.L1Nullifier.panic_error_0x11
import generated.L1Nullifier.L1Nullifier.array_allocation_size_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_decodeAssetRouterFinalizeDepositData (var_functionSignature var_messageSourceChainId var_assetId var_transferData_5881_mpos : Identifier) (var_l2ToL1message_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_decodeAssetRouterFinalizeDepositData_abs_of_concrete {s₀ s₉ : State} {var_functionSignature var_messageSourceChainId var_assetId var_transferData_5881_mpos var_l2ToL1message_mpos} :
  Spec (fun_decodeAssetRouterFinalizeDepositData_concrete_of_code.1 var_functionSignature var_messageSourceChainId var_assetId var_transferData_5881_mpos var_l2ToL1message_mpos) s₀ s₉ →
  Spec (A_fun_decodeAssetRouterFinalizeDepositData var_functionSignature var_messageSourceChainId var_assetId var_transferData_5881_mpos var_l2ToL1message_mpos) s₀ s₉ := by
  unfold A_fun_decodeAssetRouterFinalizeDepositData
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
