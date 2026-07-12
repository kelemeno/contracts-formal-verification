import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_4481893504431727677_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4481893504431727677 (s₀ s₉ : State) : Prop := sorry

lemma block_4481893504431727677_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4481893504431727677_concrete_of_code s₀ s₉ →
  Spec A_block_4481893504431727677 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
