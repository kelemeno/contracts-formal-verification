import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7014565086347997384_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_7014565086347997384 (s₀ s₉ : State) : Prop := sorry

lemma block_7014565086347997384_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7014565086347997384_concrete_of_code s₀ s₉ →
  Spec A_block_7014565086347997384 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
