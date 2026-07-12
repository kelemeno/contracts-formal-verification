import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_4897189129566826754_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4897189129566826754 (s₀ s₉ : State) : Prop := sorry

lemma if_4897189129566826754_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4897189129566826754_concrete_of_code s₀ s₉ →
  Spec A_if_4897189129566826754 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
