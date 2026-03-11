import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraTokenWithdrawal_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_isPreSharedBridgeEraTokenWithdrawal (var_ : Identifier) (var_chainId var__l2BatchNumber : Literal) (s₀ s₉ : State) : Prop :=
  fun_isPreSharedBridgeEraTokenWithdrawal_concrete_of_code.1 var_ var_chainId var__l2BatchNumber s₀ s₉

lemma fun_isPreSharedBridgeEraTokenWithdrawal_abs_of_concrete {s₀ s₉ : State} {var_ var_chainId var__l2BatchNumber} :
  Spec (fun_isPreSharedBridgeEraTokenWithdrawal_concrete_of_code.1 var_ var_chainId var__l2BatchNumber) s₀ s₉ →
  Spec (A_fun_isPreSharedBridgeEraTokenWithdrawal var_ var_chainId var__l2BatchNumber) s₀ s₉ := by
  intro h
  simpa [A_fun_isPreSharedBridgeEraTokenWithdrawal] using h

end

end generated.L1Nullifier.L1Nullifier
