import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_5297804014907174373_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5297804014907174373 (s₀ s₉ : State) : Prop := sorry

lemma block_5297804014907174373_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5297804014907174373_concrete_of_code s₀ s₉ →
  Spec A_block_5297804014907174373 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
