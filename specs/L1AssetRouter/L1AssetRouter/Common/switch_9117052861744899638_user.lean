import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_919922969513075000
import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset
import generated.L1AssetRouter.L1AssetRouter.Common.if_4114608673402717653
import generated.L1AssetRouter.L1AssetRouter.Common.if_238519235204899714
import generated.L1AssetRouter.L1AssetRouter.Common.if_3184644454673276137
import generated.L1AssetRouter.L1AssetRouter.Common.if_2117010768839705895
import generated.L1AssetRouter.L1AssetRouter.Common.if_2626124212720582549
import generated.L1AssetRouter.L1AssetRouter.Common.if_2222747483815734718
import generated.L1AssetRouter.L1AssetRouter.Common.if_4635858785563542990
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947

import generated.L1AssetRouter.L1AssetRouter.Common.switch_9117052861744899638_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_9117052861744899638 (s₀ s₉ : State) : Prop := sorry

lemma switch_9117052861744899638_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_9117052861744899638_concrete_of_code s₀ s₉ →
  Spec A_switch_9117052861744899638 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
