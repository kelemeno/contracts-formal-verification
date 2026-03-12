import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_879954185007019327

import generated.L1AssetRouter.L1AssetRouter.require_helper_error_Unauthorized_address_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_require_helper_error_Unauthorized_address  (condition expr : Literal) (s₀ s₉ : State) : Prop :=
  require_helper_error_Unauthorized_address_concrete_of_code.1 condition expr s₀ s₉

lemma require_helper_error_Unauthorized_address_abs_of_concrete {s₀ s₉ : State} { condition expr} :
  Spec (require_helper_error_Unauthorized_address_concrete_of_code.1  condition expr) s₀ s₉ →
  Spec (A_require_helper_error_Unauthorized_address  condition expr) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_Unauthorized_address] using h

end

end generated.L1AssetRouter.L1AssetRouter
