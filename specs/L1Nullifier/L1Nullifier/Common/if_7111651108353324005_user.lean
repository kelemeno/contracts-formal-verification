import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_7111651108353324005_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_7111651108353324005 (s₀ s₉ : State) : Prop :=
  if_7111651108353324005_concrete_of_code.1 s₀ s₉

lemma if_7111651108353324005_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7111651108353324005_concrete_of_code s₀ s₉ →
  Spec A_if_7111651108353324005 s₀ s₉ := by
  intro h
  simpa [A_if_7111651108353324005] using h

end

end L1Nullifier.Common
