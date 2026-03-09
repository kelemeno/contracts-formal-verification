import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4315645440235625299

import generated.L1AssetRouter.L1AssetRouter.fun_checkOwner_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_fun_checkOwner   (s₀ s₉ : State) : Prop := sorry

lemma fun_checkOwner_abs_of_concrete {s₀ s₉ : State}  :
  Spec (fun_checkOwner_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_fun_checkOwner  ) s₀ s₉ := by
  unfold fun_checkOwner_concrete_of_code A_fun_checkOwner
  sorry

end

end generated.L1AssetRouter.L1AssetRouter
