import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.abi_encode_uint256_bytes32_bytes

import generated.L2AssetRouter.L2AssetRouter.Common.block_1067437107697907065_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_1067437107697907065 (s₀ s₉ : State) : Prop := sorry

lemma block_1067437107697907065_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1067437107697907065_concrete_of_code s₀ s₉ →
  Spec A_block_1067437107697907065 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
