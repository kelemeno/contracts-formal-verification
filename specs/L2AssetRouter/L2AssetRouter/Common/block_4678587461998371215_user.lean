import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_4678587461998371215_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4678587461998371215 (s₀ s₉ : State) : Prop := block_4678587461998371215_concrete_of_code.1 s₀ s₉

lemma block_4678587461998371215_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4678587461998371215_concrete_of_code s₀ s₉ →
  Spec A_block_4678587461998371215 s₀ s₉ := by
  intro h
  simpa [A_block_4678587461998371215] using h

end

end L2AssetRouter.Common
