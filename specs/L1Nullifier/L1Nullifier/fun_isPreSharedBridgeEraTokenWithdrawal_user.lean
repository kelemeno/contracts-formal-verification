import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraTokenWithdrawal_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_isPreSharedBridgeEraTokenWithdrawal (var_ : Identifier) (var_chainId var__l2BatchNumber : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_isPreSharedBridgeEraTokenWithdrawal_abs_of_concrete {s₀ s₉ : State} {var_ var_chainId var__l2BatchNumber} :
  Spec (fun_isPreSharedBridgeEraTokenWithdrawal_concrete_of_code.1 var_ var_chainId var__l2BatchNumber) s₀ s₉ →
  Spec (A_fun_isPreSharedBridgeEraTokenWithdrawal var_ var_chainId var__l2BatchNumber) s₀ s₉ := by
  unfold A_fun_isPreSharedBridgeEraTokenWithdrawal
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
