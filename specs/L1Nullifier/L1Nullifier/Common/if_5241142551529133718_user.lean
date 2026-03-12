import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_5241142551529133718_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5241142551529133718 (s₀ s₉ : State) : Prop :=
  if_5241142551529133718_concrete_of_code.1 s₀ s₉

lemma if_5241142551529133718_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5241142551529133718_concrete_of_code s₀ s₉ →
  Spec A_if_5241142551529133718 s₀ s₉ := by
  intro h
  simpa [A_if_5241142551529133718] using h

end

end L1Nullifier.Common
