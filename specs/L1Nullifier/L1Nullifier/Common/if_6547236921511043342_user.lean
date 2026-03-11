import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_6547236921511043342_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6547236921511043342 (s₀ s₉ : State) : Prop :=
  if_6547236921511043342_concrete_of_code.1 s₀ s₉

lemma if_6547236921511043342_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6547236921511043342_concrete_of_code s₀ s₉ →
  Spec A_if_6547236921511043342 s₀ s₉ := by
  intro h
  simpa [A_if_6547236921511043342] using h

end

end L1Nullifier.Common
