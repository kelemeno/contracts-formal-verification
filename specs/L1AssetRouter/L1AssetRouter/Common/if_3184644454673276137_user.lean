import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_3184644454673276137_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3184644454673276137 (s₀ s₉ : State) : Prop :=
  if_3184644454673276137_concrete_of_code.1 s₀ s₉

lemma if_3184644454673276137_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3184644454673276137_concrete_of_code s₀ s₉ →
  Spec A_if_3184644454673276137 s₀ s₉ := by
  intro h
  simpa [A_if_3184644454673276137] using h

end

end L1AssetRouter.Common
