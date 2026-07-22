import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_7167147653621683891

import generated.L2AssetRouter.L2AssetRouter.fun_isValidInteropSender_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_fun_isValidInteropSender (var : Identifier) (var_senderChainId var_senderAddress : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_isValidInteropSender_abs_of_concrete {s₀ s₉ : State} {var var_senderChainId var_senderAddress} :
  Spec (fun_isValidInteropSender_concrete_of_code.1 var var_senderChainId var_senderAddress) s₀ s₉ →
  Spec (A_fun_isValidInteropSender var var_senderChainId var_senderAddress) s₀ s₉ := by
  unfold fun_isValidInteropSender_concrete_of_code A_fun_isValidInteropSender
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
