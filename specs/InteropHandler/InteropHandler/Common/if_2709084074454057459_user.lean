import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_2709084074454057459_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_2709084074454057459 (s₀ s₉ : State) : Prop :=
  if_2709084074454057459_concrete_of_code.1 s₀ s₉
lemma if_2709084074454057459_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2709084074454057459_concrete_of_code s₀ s₉ →
  Spec A_if_2709084074454057459 s₀ s₉ := by
  intro h
  simpa [A_if_2709084074454057459] using h

end

end InteropHandler.Common
