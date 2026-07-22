import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11718
import generated.L2AssetRouter.L2AssetRouter.convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4

import generated.L2AssetRouter.L2AssetRouter.Common.block_7237573451017549075_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_7237573451017549075 (s₀ s₉ : State) : Prop := sorry

lemma block_7237573451017549075_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7237573451017549075_concrete_of_code s₀ s₉ →
  Spec A_block_7237573451017549075 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
