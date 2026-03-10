import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_663842672556501099
import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset
import generated.L1AssetRouter.L1AssetRouter.Common.if_4114608673402717653
import generated.L1AssetRouter.L1AssetRouter.Common.if_2759842439704329415
import generated.L1AssetRouter.L1AssetRouter.Common.if_3184644454673276137
import generated.L1AssetRouter.L1AssetRouter.Common.if_8002972532267067327
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L1AssetRouter.L1AssetRouter.Common.if_7158837568111266808
import generated.L1AssetRouter.L1AssetRouter.Common.if_2654214606827169161
import generated.L1AssetRouter.L1AssetRouter.Common.if_4635858785563542990
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947

import generated.L1AssetRouter.L1AssetRouter.Common.switch_6917527303596625549_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_6917527303596625549 (s₀ s₉ : State) : Prop := True

lemma switch_6917527303596625549_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6917527303596625549_concrete_of_code s₀ s₉ →
  Spec A_switch_6917527303596625549 s₀ s₉ := by
  unfold A_switch_6917527303596625549
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
