import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_527260813423657965

import generated.L2AssetRouter.L2AssetRouter.require_helper_error_Unauthorized_address_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_require_helper_error_Unauthorized_address  (condition expr : Literal) (s₀ s₉ : State) : Prop := require_helper_error_Unauthorized_address_concrete_of_code.1 condition expr s₀ s₉

lemma require_helper_error_Unauthorized_address_abs_of_concrete {s₀ s₉ : State} { condition expr} :
  Spec (require_helper_error_Unauthorized_address_concrete_of_code.1  condition expr) s₀ s₉ →
  Spec (A_require_helper_error_Unauthorized_address  condition expr) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_Unauthorized_address] using h

end

end generated.L2AssetRouter.L2AssetRouter
