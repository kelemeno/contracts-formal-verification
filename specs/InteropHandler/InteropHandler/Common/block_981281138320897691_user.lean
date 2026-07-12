import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_981281138320897691_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_981281138320897691 (s₀ s₉ : State) : Prop := sorry

lemma block_981281138320897691_abs_of_concrete {s₀ s₉ : State} :
  Spec block_981281138320897691_concrete_of_code s₀ s₉ →
  Spec A_block_981281138320897691 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
