import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_1049666816816493607

import generated.L2AssetRouter.L2AssetRouter.require_helper_error_InteropSenderChainIdMismatch_uint256_uint256_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_require_helper_error_InteropSenderChainIdMismatch_uint256_uint256  (condition expr expr_1 : Literal) (s₀ s₉ : State) : Prop := require_helper_error_InteropSenderChainIdMismatch_uint256_uint256_concrete_of_code.1 condition expr expr_1 s₀ s₉

lemma require_helper_error_InteropSenderChainIdMismatch_uint256_uint256_abs_of_concrete {s₀ s₉ : State} { condition expr expr_1} :
  Spec (require_helper_error_InteropSenderChainIdMismatch_uint256_uint256_concrete_of_code.1  condition expr expr_1) s₀ s₉ →
  Spec (A_require_helper_error_InteropSenderChainIdMismatch_uint256_uint256  condition expr expr_1) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_InteropSenderChainIdMismatch_uint256_uint256] using h

end

end generated.L2AssetRouter.L2AssetRouter
