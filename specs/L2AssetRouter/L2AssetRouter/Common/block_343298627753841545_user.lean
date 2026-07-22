import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_343298627753841545_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_343298627753841545 (s₀ s₉ : State) : Prop := sorry

lemma block_343298627753841545_abs_of_concrete {s₀ s₉ : State} :
  Spec block_343298627753841545_concrete_of_code s₀ s₉ →
  Spec A_block_343298627753841545 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
