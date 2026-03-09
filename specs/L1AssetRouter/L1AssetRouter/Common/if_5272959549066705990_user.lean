import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_5272959549066705990_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5272959549066705990 (s₀ s₉ : State) : Prop := sorry

lemma if_5272959549066705990_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5272959549066705990_concrete_of_code s₀ s₉ →
  Spec A_if_5272959549066705990 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
