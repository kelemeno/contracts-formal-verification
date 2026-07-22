import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.constant_L2_BRIDGEHUB_ADDR
import generated.L2AssetRouter.L2AssetRouter.cleanup_address

import generated.L2AssetRouter.L2AssetRouter.Common.block_4011585858768310270_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_4011585858768310270 (s₀ s₉ : State) : Prop := sorry

lemma block_4011585858768310270_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4011585858768310270_concrete_of_code s₀ s₉ →
  Spec A_block_4011585858768310270 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
