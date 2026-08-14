import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_3995168818704772226_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_3995168818704772226 (s₀ s₉ : State) : Prop :=
  if_3995168818704772226_concrete_of_code.1 s₀ s₉
lemma if_3995168818704772226_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3995168818704772226_concrete_of_code s₀ s₉ →
  Spec A_if_3995168818704772226 s₀ s₉ := by
  intro h
  simpa [A_if_3995168818704772226] using h

end

end InteropHandler.Common
