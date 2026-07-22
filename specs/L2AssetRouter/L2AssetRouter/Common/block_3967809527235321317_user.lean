import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_3967809527235321317_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3967809527235321317 (s₀ s₉ : State) : Prop := sorry

lemma block_3967809527235321317_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3967809527235321317_concrete_of_code s₀ s₉ →
  Spec A_block_3967809527235321317 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
