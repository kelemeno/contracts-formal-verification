import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_1986012260634366082

import generated.L1Nullifier.L1Nullifier.fun_verifyCallResultFromTarget_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_verifyCallResultFromTarget (var_mpos : Identifier) (var_target var_success var_returndata_mpos var_errorMessage_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_verifyCallResultFromTarget_abs_of_concrete {s₀ s₉ : State} {var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos} :
  Spec (fun_verifyCallResultFromTarget_concrete_of_code.1 var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos) s₀ s₉ →
  Spec (A_fun_verifyCallResultFromTarget var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos) s₀ s₉ := by
  unfold fun_verifyCallResultFromTarget_concrete_of_code A_fun_verifyCallResultFromTarget
  sorry

end

end generated.L1Nullifier.L1Nullifier
