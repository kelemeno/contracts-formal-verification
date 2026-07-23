import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.if_1273033159834355241_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1273033159834355241 (s₀ s₉ : State) : Prop := if_1273033159834355241_concrete_of_code.1 s₀ s₉

lemma if_1273033159834355241_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1273033159834355241_concrete_of_code s₀ s₉ →
  Spec A_if_1273033159834355241 s₀ s₉ := by
  intro h
  simpa [A_if_1273033159834355241] using h

end

end L2InteropHandler.Common
