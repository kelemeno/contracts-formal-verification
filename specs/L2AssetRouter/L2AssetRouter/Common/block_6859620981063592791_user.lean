import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_6859620981063592791_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_6859620981063592791 (s₀ s₉ : State) : Prop := sorry

lemma block_6859620981063592791_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6859620981063592791_concrete_of_code s₀ s₉ →
  Spec A_block_6859620981063592791 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
