import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5528132988775090082
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_4774653403140989705
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable
import generated.L1AssetRouter.L1AssetRouter.fun_ensureTokenRegisteredWithNTV
import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId
import generated.L1AssetRouter.L1AssetRouter.Common.if_6882868766392847326
import generated.L1AssetRouter.L1AssetRouter.Common.if_2507078964606319426
import generated.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData

import generated.L1AssetRouter.L1AssetRouter.Common.switch_4675297000597642223_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_4675297000597642223 (s₀ s₉ : State) : Prop := True

lemma switch_4675297000597642223_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4675297000597642223_concrete_of_code s₀ s₉ →
  Spec A_switch_4675297000597642223 s₀ s₉ := by
  unfold A_switch_4675297000597642223
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common
