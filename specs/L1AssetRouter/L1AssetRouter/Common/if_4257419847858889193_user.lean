import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_4257419847858889193_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4257419847858889193 (s₀ s₉ : State) : Prop := sorry

lemma if_4257419847858889193_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4257419847858889193_concrete_of_code s₀ s₉ →
  Spec A_if_4257419847858889193 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
