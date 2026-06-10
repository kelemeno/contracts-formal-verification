import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_5909921818141361415_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5909921818141361415 (s₀ s₉ : State) : Prop := block_5909921818141361415_concrete_of_code.1 s₀ s₉

lemma block_5909921818141361415_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5909921818141361415_concrete_of_code s₀ s₉ →
  Spec A_block_5909921818141361415 s₀ s₉ := by
  intro h
  simpa [A_block_5909921818141361415] using h

end

end L1AssetRouter.Common
