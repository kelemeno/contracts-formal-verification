import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeDepositOnEra_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_isPreSharedBridgeDepositOnEra (var : Identifier) (var_chainId var_l2BatchNumber var_l2TxNumberInBatch : Literal) (s₀ s₉ : State) : Prop :=
  fun_isPreSharedBridgeDepositOnEra_concrete_of_code.1 var var_chainId var_l2BatchNumber var_l2TxNumberInBatch s₀ s₉

lemma fun_isPreSharedBridgeDepositOnEra_abs_of_concrete {s₀ s₉ : State} {var var_chainId var_l2BatchNumber var_l2TxNumberInBatch} :
  Spec (fun_isPreSharedBridgeDepositOnEra_concrete_of_code.1 var var_chainId var_l2BatchNumber var_l2TxNumberInBatch) s₀ s₉ →
  Spec (A_fun_isPreSharedBridgeDepositOnEra var var_chainId var_l2BatchNumber var_l2TxNumberInBatch) s₀ s₉ := by
  intro h
  simpa [A_fun_isPreSharedBridgeDepositOnEra] using h

end

end generated.L1Nullifier.L1Nullifier
