import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes

import generated.L2AssetRouter.L2AssetRouter.Common.block_5514941267674449130_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_5514941267674449130 (s₀ s₉ : State) : Prop := sorry

lemma block_5514941267674449130_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5514941267674449130_concrete_of_code s₀ s₉ →
  Spec A_block_5514941267674449130 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
