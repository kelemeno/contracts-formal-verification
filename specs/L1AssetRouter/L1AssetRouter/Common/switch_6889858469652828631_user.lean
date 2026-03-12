import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_6806349311392857852
import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset
import generated.L1AssetRouter.L1AssetRouter.Common.if_4114608673402717653
import generated.L1AssetRouter.L1AssetRouter.Common.if_2608270739739303682
import generated.L1AssetRouter.L1AssetRouter.Common.if_3184644454673276137
import generated.L1AssetRouter.L1AssetRouter.Common.if_2117010768839705895
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L1AssetRouter.L1AssetRouter.Common.if_2626124212720582549
import generated.L1AssetRouter.L1AssetRouter.Common.if_5876042495792135430
import generated.L1AssetRouter.L1AssetRouter.Common.if_4635858785563542990
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947

import generated.L1AssetRouter.L1AssetRouter.Common.switch_6889858469652828631_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_6889858469652828631 (s₀ s₉ : State) : Prop :=
  switch_6889858469652828631_concrete_of_code.1 s₀ s₉

lemma switch_6889858469652828631_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6889858469652828631_concrete_of_code s₀ s₉ →
  Spec A_switch_6889858469652828631 s₀ s₉ := by
  intro h
  simpa [A_switch_6889858469652828631] using h

end

end L1AssetRouter.Common
