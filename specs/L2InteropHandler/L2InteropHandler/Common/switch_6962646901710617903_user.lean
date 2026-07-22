import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.switch_6962646901710617903_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_6962646901710617903 (s₀ s₉ : State) : Prop := sorry

lemma switch_6962646901710617903_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6962646901710617903_concrete_of_code s₀ s₉ →
  Spec A_switch_6962646901710617903 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
