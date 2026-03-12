import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_4919737637054797426_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4919737637054797426 (s₀ s₉ : State) : Prop :=
  if_4919737637054797426_concrete_of_code.1 s₀ s₉

lemma if_4919737637054797426_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4919737637054797426_concrete_of_code s₀ s₉ →
  Spec A_if_4919737637054797426 s₀ s₉ := by
  intro h
  simpa [A_if_4919737637054797426] using h

end

end L1AssetRouter.Common
