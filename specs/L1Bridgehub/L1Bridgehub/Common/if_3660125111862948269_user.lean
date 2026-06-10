import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.Common.if_3660125111862948269_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3660125111862948269 (s₀ s₉ : State) : Prop := if_3660125111862948269_concrete_of_code.1 s₀ s₉

lemma if_3660125111862948269_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3660125111862948269_concrete_of_code s₀ s₉ →
  Spec A_if_3660125111862948269 s₀ s₉ := by
  intro h
  simpa [A_if_3660125111862948269] using h

end

end L1Bridgehub.Common
