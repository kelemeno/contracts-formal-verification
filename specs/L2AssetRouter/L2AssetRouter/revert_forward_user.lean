import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.revert_forward_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_revert_forward   (s₀ s₉ : State) : Prop := revert_forward_concrete_of_code.1 s₀ s₉

lemma revert_forward_abs_of_concrete {s₀ s₉ : State}  :
  Spec (revert_forward_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_revert_forward  ) s₀ s₉ := by
  intro h
  simpa [A_revert_forward] using h

end

end generated.L2AssetRouter.L2AssetRouter
