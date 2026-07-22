import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4011426281918827344

import generated.L2AssetRouter.L2AssetRouter.require_helper_error_PayloadTooShort_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_require_helper_error_PayloadTooShort  (condition : Literal) (s₀ s₉ : State) : Prop := sorry

lemma require_helper_error_PayloadTooShort_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_error_PayloadTooShort_concrete_of_code.1  condition) s₀ s₉ →
  Spec (A_require_helper_error_PayloadTooShort  condition) s₀ s₉ := by
  unfold require_helper_error_PayloadTooShort_concrete_of_code A_require_helper_error_PayloadTooShort
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
