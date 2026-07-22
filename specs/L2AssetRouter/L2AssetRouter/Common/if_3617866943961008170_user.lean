import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.if_3617866943961008170_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3617866943961008170 (s₀ s₉ : State) : Prop := sorry

lemma if_3617866943961008170_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3617866943961008170_concrete_of_code s₀ s₉ →
  Spec A_if_3617866943961008170 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
