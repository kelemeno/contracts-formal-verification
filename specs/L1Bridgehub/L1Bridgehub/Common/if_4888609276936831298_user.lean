import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.Common.if_4888609276936831298_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4888609276936831298 (s₀ s₉ : State) : Prop := if_4888609276936831298_concrete_of_code.1 s₀ s₉

lemma if_4888609276936831298_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4888609276936831298_concrete_of_code s₀ s₉ →
  Spec A_if_4888609276936831298 s₀ s₉ := by
  intro h
  simpa [A_if_4888609276936831298] using h

end

end L1Bridgehub.Common
