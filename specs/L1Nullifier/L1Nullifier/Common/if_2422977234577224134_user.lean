import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_2422977234577224134_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_2422977234577224134 (s₀ s₉ : State) : Prop := sorry

lemma if_2422977234577224134_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2422977234577224134_concrete_of_code s₀ s₉ →
  Spec A_if_2422977234577224134 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
