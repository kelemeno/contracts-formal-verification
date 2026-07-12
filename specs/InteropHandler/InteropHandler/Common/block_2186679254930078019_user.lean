import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2186679254930078019_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2186679254930078019 (s₀ s₉ : State) : Prop := sorry

lemma block_2186679254930078019_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2186679254930078019_concrete_of_code s₀ s₉ →
  Spec A_block_2186679254930078019 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
