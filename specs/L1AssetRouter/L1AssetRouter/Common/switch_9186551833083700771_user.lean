import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8145808823390256759
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.mcopy
import generated.L1AssetRouter.L1AssetRouter.Common.if_8090077789747370802
import generated.L1AssetRouter.L1AssetRouter.Common.if_6602275548560376283
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId
import generated.L1AssetRouter.L1AssetRouter.Common.if_3393679758987507345
import generated.L1AssetRouter.L1AssetRouter.Common.if_6478595247897345129
import generated.L1AssetRouter.L1AssetRouter.Common.if_7399798940655740021
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256

import generated.L1AssetRouter.L1AssetRouter.Common.switch_9186551833083700771_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_9186551833083700771 (s₀ s₉ : State) : Prop := sorry

lemma switch_9186551833083700771_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_9186551833083700771_concrete_of_code s₀ s₉ →
  Spec A_switch_9186551833083700771 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
