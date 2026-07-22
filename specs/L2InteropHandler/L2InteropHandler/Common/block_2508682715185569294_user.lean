import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.block_2508682715185569294_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2508682715185569294 (s₀ s₉ : State) : Prop := sorry

lemma block_2508682715185569294_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2508682715185569294_concrete_of_code s₀ s₉ →
  Spec A_block_2508682715185569294 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common
