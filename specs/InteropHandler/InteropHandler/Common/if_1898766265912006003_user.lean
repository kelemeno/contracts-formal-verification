import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_1898766265912006003_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1898766265912006003 (s₀ s₉ : State) : Prop := sorry

lemma if_1898766265912006003_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1898766265912006003_concrete_of_code s₀ s₉ →
  Spec A_if_1898766265912006003 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
