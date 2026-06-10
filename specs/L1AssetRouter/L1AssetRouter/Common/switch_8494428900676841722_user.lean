import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5528132988775090082
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_4774653403140989705
import generated.L1AssetRouter.L1AssetRouter.Common.block_1226142334069022207
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable
import generated.L1AssetRouter.L1AssetRouter.Common.block_1699957725972452821
import generated.L1AssetRouter.L1AssetRouter.fun_ensureTokenRegisteredWithNTV
import generated.L1AssetRouter.L1AssetRouter.Common.block_8571920284540918175
import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId
import generated.L1AssetRouter.L1AssetRouter.Common.if_6882868766392847326
import generated.L1AssetRouter.L1AssetRouter.Common.if_2507078964606319426
import generated.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8494428900676841722_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_8494428900676841722 (s₀ s₉ : State) : Prop := switch_8494428900676841722_concrete_of_code.1 s₀ s₉

lemma switch_8494428900676841722_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8494428900676841722_concrete_of_code s₀ s₉ →
  Spec A_switch_8494428900676841722 s₀ s₉ := by
  intro h
  simpa [A_switch_8494428900676841722] using h

end

end L1AssetRouter.Common
