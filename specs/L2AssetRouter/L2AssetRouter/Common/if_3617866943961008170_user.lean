import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.if_3617866943961008170_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3617866943961008170 (s₀ s₉ : State) : Prop := if_3617866943961008170_concrete_of_code.1 s₀ s₉

lemma if_3617866943961008170_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3617866943961008170_concrete_of_code s₀ s₉ →
  Spec A_if_3617866943961008170 s₀ s₉ := by
  intro h
  simpa [A_if_3617866943961008170] using h

end

end L2AssetRouter.Common
