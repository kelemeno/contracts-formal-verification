import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5291372013835548049
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.mcopy
import generated.L1AssetRouter.L1AssetRouter.Common.if_85418916146971295
import generated.L1AssetRouter.L1AssetRouter.Common.if_8235423303573985762
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_3119235993534743194
import generated.L1AssetRouter.L1AssetRouter.Common.if_2721767499933224978
import generated.L1AssetRouter.L1AssetRouter.Common.if_6003871829001462819

import generated.L1AssetRouter.L1AssetRouter.Common.switch_3962063832550925794_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_3962063832550925794 (s₀ s₉ : State) : Prop := sorry

lemma switch_3962063832550925794_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3962063832550925794_concrete_of_code s₀ s₉ →
  Spec A_switch_3962063832550925794 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
