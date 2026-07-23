import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.if_308632468716969556_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_308632468716969556 (s₀ s₉ : State) : Prop := if_308632468716969556_concrete_of_code.1 s₀ s₉

lemma if_308632468716969556_abs_of_concrete {s₀ s₉ : State} :
  Spec if_308632468716969556_concrete_of_code s₀ s₉ →
  Spec A_if_308632468716969556 s₀ s₉ := by
  intro h
  simpa [A_if_308632468716969556] using h

end

end L2InteropHandler.Common
