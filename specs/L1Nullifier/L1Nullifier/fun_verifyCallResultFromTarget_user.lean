import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_verifyCallResultFromTarget_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_verifyCallResultFromTarget (var_mpos : Identifier) (var_target var_success var_returndata_mpos var_errorMessage_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_verifyCallResultFromTarget_abs_of_concrete {s₀ s₉ : State} {var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos} :
  Spec (fun_verifyCallResultFromTarget_concrete_of_code.1 var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos) s₀ s₉ →
  Spec (A_fun_verifyCallResultFromTarget var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos) s₀ s₉ := by
  unfold A_fun_verifyCallResultFromTarget
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier
