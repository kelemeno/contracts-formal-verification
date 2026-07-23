import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_1800147066814770297

import generated.L2InteropHandler.L2InteropHandler.Common.if_1741946688071961186_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_if_1741946688071961186 (s₀ s₉ : State) : Prop := if_1741946688071961186_concrete_of_code.1 s₀ s₉

lemma if_1741946688071961186_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1741946688071961186_concrete_of_code s₀ s₉ →
  Spec A_if_1741946688071961186 s₀ s₉ := by
  intro h
  simpa [A_if_1741946688071961186] using h

end

end L2InteropHandler.Common
