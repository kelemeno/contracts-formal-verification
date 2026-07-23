import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_4822775801670294296_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4822775801670294296 (s₀ s₉ : State) : Prop := block_4822775801670294296_concrete_of_code.1 s₀ s₉

lemma block_4822775801670294296_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4822775801670294296_concrete_of_code s₀ s₉ →
  Spec A_block_4822775801670294296 s₀ s₉ := by
  intro h
  simpa [A_block_4822775801670294296] using h

end

end L2AssetRouter.Common
