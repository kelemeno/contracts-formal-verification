import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_7237573451017549075
import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_range_access_bytes_calldata_11718
import generated.L2AssetRouter.L2AssetRouter.convert_bytes_to_fixedbytes_from_bytes_calldata_to_bytes4
import generated.L2AssetRouter.L2AssetRouter.Common.block_2129288043697879337

import generated.L2AssetRouter.L2AssetRouter.Common.if_9037085336587543485_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_if_9037085336587543485 (s₀ s₉ : State) : Prop := if_9037085336587543485_concrete_of_code.1 s₀ s₉

lemma if_9037085336587543485_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9037085336587543485_concrete_of_code s₀ s₉ →
  Spec A_if_9037085336587543485 s₀ s₉ := by
  intro h
  simpa [A_if_9037085336587543485] using h

end

end L2AssetRouter.Common
