import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_9153090929313368865_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_9153090929313368865 (s₀ s₉ : State) : Prop := sorry

lemma if_9153090929313368865_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9153090929313368865_concrete_of_code s₀ s₉ →
  Spec A_if_9153090929313368865 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
