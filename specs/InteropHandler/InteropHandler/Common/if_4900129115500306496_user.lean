import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_4900129115500306496_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_4900129115500306496 (s₀ s₉ : State) : Prop :=
  if_4900129115500306496_concrete_of_code.1 s₀ s₉
lemma if_4900129115500306496_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4900129115500306496_concrete_of_code s₀ s₉ →
  Spec A_if_4900129115500306496 s₀ s₉ := by
  intro h
  simpa [A_if_4900129115500306496] using h

end

end InteropHandler.Common
