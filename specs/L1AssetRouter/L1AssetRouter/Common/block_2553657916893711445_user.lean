import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_2553657916893711445_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2553657916893711445 (s₀ s₉ : State) : Prop := block_2553657916893711445_concrete_of_code.1 s₀ s₉

lemma block_2553657916893711445_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2553657916893711445_concrete_of_code s₀ s₉ →
  Spec A_block_2553657916893711445 s₀ s₉ := by
  intro h
  simpa [A_block_2553657916893711445] using h

end

end L1AssetRouter.Common
