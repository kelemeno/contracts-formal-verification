import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_3485639593616020660_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3485639593616020660 (s₀ s₉ : State) : Prop := sorry

lemma if_3485639593616020660_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3485639593616020660_concrete_of_code s₀ s₉ →
  Spec A_if_3485639593616020660 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
