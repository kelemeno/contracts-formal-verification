import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_8322446248705927466
import generated.L1AssetRouter.L1AssetRouter.Common.if_1996614206653605388
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256
import generated.L1AssetRouter.L1AssetRouter.Common.switch_3487672722122768183
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.Common.if_3169290594777010327
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_3074696543832101371
import generated.L1AssetRouter.L1AssetRouter.Common.if_6612257451548554226
import generated.L1AssetRouter.L1AssetRouter.Common.if_1254062856785940686
import generated.L1AssetRouter.L1AssetRouter.Common.if_1850768182690122168
import generated.L1AssetRouter.L1AssetRouter.Common.if_3512591431497983588

import generated.L1AssetRouter.L1AssetRouter.Common.if_2338892551544939949_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_2338892551544939949 (s₀ s₉ : State) : Prop := sorry

lemma if_2338892551544939949_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2338892551544939949_concrete_of_code s₀ s₉ →
  Spec A_if_2338892551544939949 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
