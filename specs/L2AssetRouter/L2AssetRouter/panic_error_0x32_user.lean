import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_panic_error_0x32   (s₀ s₉ : State) : Prop := sorry

lemma panic_error_0x32_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x32_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x32  ) s₀ s₉ := by
  unfold panic_error_0x32_concrete_of_code A_panic_error_0x32
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
