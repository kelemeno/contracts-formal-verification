import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4441247777815182798

import generated.L1AssetRouter.L1AssetRouter.require_helper_error_Unauthorized_address_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_require_helper_error_Unauthorized_address  (condition expr : Literal) (s₀ s₉ : State) : Prop := True

lemma require_helper_error_Unauthorized_address_abs_of_concrete {s₀ s₉ : State} { condition expr} :
  Spec (require_helper_error_Unauthorized_address_concrete_of_code.1  condition expr) s₀ s₉ →
  Spec (A_require_helper_error_Unauthorized_address  condition expr) s₀ s₉ := by
  unfold require_helper_error_Unauthorized_address_concrete_of_code A_require_helper_error_Unauthorized_address
  unfold A_require_helper_error_Unauthorized_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
