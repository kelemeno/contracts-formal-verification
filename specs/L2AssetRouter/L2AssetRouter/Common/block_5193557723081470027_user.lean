import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L2AssetRouter.L2AssetRouter.calldata_array_index_access_bytes_calldata_11804
import generated.L2AssetRouter.L2AssetRouter.fun_decodeAssetRouterBridgehubDepositData

import generated.L2AssetRouter.L2AssetRouter.Common.block_5193557723081470027_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_5193557723081470027 (s₀ s₉ : State) : Prop := block_5193557723081470027_concrete_of_code.1 s₀ s₉

lemma block_5193557723081470027_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5193557723081470027_concrete_of_code s₀ s₉ →
  Spec A_block_5193557723081470027 s₀ s₉ := by
  intro h
  simpa [A_block_5193557723081470027] using h

end

end L2AssetRouter.Common
