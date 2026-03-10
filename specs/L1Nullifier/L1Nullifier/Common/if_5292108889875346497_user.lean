import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_5292108889875346497_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5292108889875346497 (s₀ s₉ : State) : Prop := sorry

lemma if_5292108889875346497_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5292108889875346497_concrete_of_code s₀ s₉ →
  Spec A_if_5292108889875346497 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common
