import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_1167488127832011495_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_1167488127832011495 (s₀ s₉ : State) : Prop := block_1167488127832011495_concrete_of_code.1 s₀ s₉

lemma block_1167488127832011495_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1167488127832011495_concrete_of_code s₀ s₉ →
  Spec A_block_1167488127832011495 s₀ s₉ := by
  intro h
  simpa [A_block_1167488127832011495] using h

end

end L1AssetRouter.Common
