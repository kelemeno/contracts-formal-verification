import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.if_5948157386607140920_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5948157386607140920 (s₀ s₉ : State) : Prop := sorry

lemma if_5948157386607140920_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5948157386607140920_concrete_of_code s₀ s₉ →
  Spec A_if_5948157386607140920 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
