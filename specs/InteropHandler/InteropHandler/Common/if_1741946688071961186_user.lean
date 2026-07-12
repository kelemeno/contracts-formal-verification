import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_1800147066814770297

import generated.InteropHandler.InteropHandler.Common.if_1741946688071961186_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_if_1741946688071961186 (s₀ s₉ : State) : Prop := sorry

lemma if_1741946688071961186_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1741946688071961186_concrete_of_code s₀ s₉ →
  Spec A_if_1741946688071961186 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
