import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_6547236921511043342

import generated.L1AssetRouter.L1AssetRouter.fun_requireNotPaused_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_fun_requireNotPaused   (s₀ s₉ : State) : Prop :=
  fun_requireNotPaused_concrete_of_code.1 s₀ s₉

lemma fun_requireNotPaused_abs_of_concrete {s₀ s₉ : State}  :
  Spec (fun_requireNotPaused_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_fun_requireNotPaused  ) s₀ s₉ := by
  intro h
  simpa [A_fun_requireNotPaused] using h

end

end generated.L1AssetRouter.L1AssetRouter
