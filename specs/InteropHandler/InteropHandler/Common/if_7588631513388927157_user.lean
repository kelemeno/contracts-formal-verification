import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_7588631513388927157_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_7588631513388927157 (s₀ s₉ : State) : Prop := sorry

lemma if_7588631513388927157_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7588631513388927157_concrete_of_code s₀ s₉ →
  Spec A_if_7588631513388927157 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
