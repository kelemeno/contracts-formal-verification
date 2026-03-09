import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_5825100901815297108
import generated.L1Nullifier.L1Nullifier.Common.if_4417306148967690011
import generated.L1Nullifier.L1Nullifier.Common.if_7035037884904118640

import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraTokenWithdrawal_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_isPreSharedBridgeEraTokenWithdrawal (var_ : Identifier) (var_chainId var__l2BatchNumber : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_isPreSharedBridgeEraTokenWithdrawal_abs_of_concrete {s₀ s₉ : State} {var_ var_chainId var__l2BatchNumber} :
  Spec (fun_isPreSharedBridgeEraTokenWithdrawal_concrete_of_code.1 var_ var_chainId var__l2BatchNumber) s₀ s₉ →
  Spec (A_fun_isPreSharedBridgeEraTokenWithdrawal var_ var_chainId var__l2BatchNumber) s₀ s₉ := by
  unfold fun_isPreSharedBridgeEraTokenWithdrawal_concrete_of_code A_fun_isPreSharedBridgeEraTokenWithdrawal
  sorry

end

end generated.L1Nullifier.L1Nullifier
