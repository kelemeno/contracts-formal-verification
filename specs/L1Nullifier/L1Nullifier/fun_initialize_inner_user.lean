import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.require_helper_error_ZeroAddress
import generated.L1Nullifier.L1Nullifier.fun_transferOwnership

import generated.L1Nullifier.L1Nullifier.fun_initialize_inner_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_initialize_inner  (var_owner var_eraPostDiamondUpgradeFirstBatch var_eraPostLegacyBridgeUpgradeFirstBatch var_eraLegacyBridgeLastDepositBatch var_eraLegacyBridgeLastDepositTxNumber : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_initialize_inner_abs_of_concrete {s₀ s₉ : State} { var_owner var_eraPostDiamondUpgradeFirstBatch var_eraPostLegacyBridgeUpgradeFirstBatch var_eraLegacyBridgeLastDepositBatch var_eraLegacyBridgeLastDepositTxNumber} :
  Spec (fun_initialize_inner_concrete_of_code.1 var_owner var_eraPostDiamondUpgradeFirstBatch var_eraPostLegacyBridgeUpgradeFirstBatch var_eraLegacyBridgeLastDepositBatch var_eraLegacyBridgeLastDepositTxNumber) s₀ s₉ →
  Spec (A_fun_initialize_inner var_owner var_eraPostDiamondUpgradeFirstBatch var_eraPostLegacyBridgeUpgradeFirstBatch var_eraLegacyBridgeLastDepositBatch var_eraLegacyBridgeLastDepositTxNumber) s₀ s₉ := by
  unfold A_fun_initialize_inner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
