import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_8365987808918906782_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_8365987808918906782 (s₀ s₉ : State) : Prop :=
  if_8365987808918906782_concrete_of_code.1 s₀ s₉

lemma if_8365987808918906782_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8365987808918906782_concrete_of_code s₀ s₉ →
  Spec A_if_8365987808918906782 s₀ s₉ := by
  intro h
  simpa [A_if_8365987808918906782] using h

end

end L1Nullifier.Common
