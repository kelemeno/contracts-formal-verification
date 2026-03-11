import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_3515090449336820943_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3515090449336820943 (s₀ s₉ : State) : Prop :=
  if_3515090449336820943_concrete_of_code.1 s₀ s₉

lemma if_3515090449336820943_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3515090449336820943_concrete_of_code s₀ s₉ →
  Spec A_if_3515090449336820943 s₀ s₉ := by
  intro h
  simpa [A_if_3515090449336820943] using h

end

end L1AssetRouter.Common
