import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_access_bytes_calldata
import generated.L2AssetRouter.L2AssetRouter.cleanup_bytes1
import generated.L2AssetRouter.L2AssetRouter.convert_bytes1_to_uint8
import generated.L2AssetRouter.L2AssetRouter.extract_from_storage_value_offset_bool

import generated.L2AssetRouter.L2AssetRouter.Common.block_5212034964361298986_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_5212034964361298986 (s₀ s₉ : State) : Prop := sorry

lemma block_5212034964361298986_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5212034964361298986_concrete_of_code s₀ s₉ →
  Spec A_block_5212034964361298986 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
