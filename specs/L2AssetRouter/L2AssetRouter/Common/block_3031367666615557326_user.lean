import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_3031367666615557326_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3031367666615557326 (s₀ s₉ : State) : Prop := sorry

lemma block_3031367666615557326_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3031367666615557326_concrete_of_code s₀ s₉ →
  Spec A_block_3031367666615557326 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
