import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.switch_5364585472786756111

import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_fun_verifyCallResultFromTarget (var_mpos : Identifier) (var_target var_success var_returndata_mpos var_errorMessage_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_verifyCallResultFromTarget_concrete_of_code.1 var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos s₀ s₉

lemma fun_verifyCallResultFromTarget_abs_of_concrete {s₀ s₉ : State} {var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos} :
  Spec (fun_verifyCallResultFromTarget_concrete_of_code.1 var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos) s₀ s₉ →
  Spec (A_fun_verifyCallResultFromTarget var_mpos var_target var_success var_returndata_mpos var_errorMessage_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_verifyCallResultFromTarget] using h

end

end generated.L1AssetRouter.L1AssetRouter
