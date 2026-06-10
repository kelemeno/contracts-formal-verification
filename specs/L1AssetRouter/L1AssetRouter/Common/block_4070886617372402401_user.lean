import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_4070886617372402401_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4070886617372402401 (s₀ s₉ : State) : Prop := block_4070886617372402401_concrete_of_code.1 s₀ s₉

lemma block_4070886617372402401_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4070886617372402401_concrete_of_code s₀ s₉ →
  Spec A_block_4070886617372402401 s₀ s₉ := by
  intro h
  simpa [A_block_4070886617372402401] using h

end

end L1AssetRouter.Common
