import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_5568105450979583177_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5568105450979583177 (s₀ s₉ : State) : Prop := sorry

lemma block_5568105450979583177_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5568105450979583177_concrete_of_code s₀ s₉ →
  Spec A_block_5568105450979583177 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
