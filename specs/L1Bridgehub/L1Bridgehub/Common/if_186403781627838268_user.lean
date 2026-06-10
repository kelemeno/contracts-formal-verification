import Clear.ReasoningPrinciple


import generated.L1Bridgehub.L1Bridgehub.Common.if_186403781627838268_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_186403781627838268 (s₀ s₉ : State) : Prop := if_186403781627838268_concrete_of_code.1 s₀ s₉

lemma if_186403781627838268_abs_of_concrete {s₀ s₉ : State} :
  Spec if_186403781627838268_concrete_of_code s₀ s₉ →
  Spec A_if_186403781627838268 s₀ s₉ := by
  intro h
  simpa [A_if_186403781627838268] using h

end

end L1Bridgehub.Common
