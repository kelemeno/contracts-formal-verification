import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_5474211939461848641_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5474211939461848641 (s₀ s₉ : State) : Prop := sorry

lemma if_5474211939461848641_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5474211939461848641_concrete_of_code s₀ s₉ →
  Spec A_if_5474211939461848641 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
