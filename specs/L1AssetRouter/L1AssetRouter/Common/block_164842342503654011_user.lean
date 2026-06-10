import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_164842342503654011_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_164842342503654011 (s₀ s₉ : State) : Prop := block_164842342503654011_concrete_of_code.1 s₀ s₉

lemma block_164842342503654011_abs_of_concrete {s₀ s₉ : State} :
  Spec block_164842342503654011_concrete_of_code s₀ s₉ →
  Spec A_block_164842342503654011 s₀ s₉ := by
  intro h
  simpa [A_block_164842342503654011] using h

end

end L1AssetRouter.Common
