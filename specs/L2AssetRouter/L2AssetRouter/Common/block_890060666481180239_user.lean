import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_890060666481180239_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_890060666481180239 (s₀ s₉ : State) : Prop := sorry

lemma block_890060666481180239_abs_of_concrete {s₀ s₉ : State} :
  Spec block_890060666481180239_concrete_of_code s₀ s₉ →
  Spec A_block_890060666481180239 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
