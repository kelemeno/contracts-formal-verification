import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.if_1947313727863088020_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1947313727863088020 (s₀ s₉ : State) : Prop := sorry

lemma if_1947313727863088020_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1947313727863088020_concrete_of_code s₀ s₉ →
  Spec A_if_1947313727863088020 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
