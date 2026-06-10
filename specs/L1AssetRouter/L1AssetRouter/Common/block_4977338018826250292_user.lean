import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_4977338018826250292_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4977338018826250292 (s₀ s₉ : State) : Prop := block_4977338018826250292_concrete_of_code.1 s₀ s₉

lemma block_4977338018826250292_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4977338018826250292_concrete_of_code s₀ s₉ →
  Spec A_block_4977338018826250292 s₀ s₉ := by
  intro h
  simpa [A_block_4977338018826250292] using h

end

end L1AssetRouter.Common
