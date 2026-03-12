import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_1117783195986662844_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1117783195986662844 (s₀ s₉ : State) : Prop :=
  if_1117783195986662844_concrete_of_code.1 s₀ s₉

lemma if_1117783195986662844_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1117783195986662844_concrete_of_code s₀ s₉ →
  Spec A_if_1117783195986662844 s₀ s₉ := by
  intro h
  simpa [A_if_1117783195986662844] using h

end

end L1AssetRouter.Common
