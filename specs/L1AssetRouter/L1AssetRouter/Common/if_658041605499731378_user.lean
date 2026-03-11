import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_658041605499731378_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_658041605499731378 (s₀ s₉ : State) : Prop :=
  if_658041605499731378_concrete_of_code.1 s₀ s₉

lemma if_658041605499731378_abs_of_concrete {s₀ s₉ : State} :
  Spec if_658041605499731378_concrete_of_code s₀ s₉ →
  Spec A_if_658041605499731378 s₀ s₉ := by
  intro h
  simpa [A_if_658041605499731378] using h

end

end L1AssetRouter.Common
