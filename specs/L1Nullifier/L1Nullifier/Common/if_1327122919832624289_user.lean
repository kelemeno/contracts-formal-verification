import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_1327122919832624289_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_1327122919832624289 (s₀ s₉ : State) : Prop := sorry

lemma if_1327122919832624289_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1327122919832624289_concrete_of_code s₀ s₉ →
  Spec A_if_1327122919832624289 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
