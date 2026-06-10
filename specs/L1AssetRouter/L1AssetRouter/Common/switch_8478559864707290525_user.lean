import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_5182448773037313770
import generated.L1AssetRouter.L1AssetRouter.Common.block_5796613295154141460
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_4521731106176019512
import generated.L1AssetRouter.L1AssetRouter.Common.if_5718206110945243169
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_138469769776544866
import generated.L1AssetRouter.L1AssetRouter.Common.if_6347281329581904638

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8478559864707290525_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_8478559864707290525 (s₀ s₉ : State) : Prop := switch_8478559864707290525_concrete_of_code.1 s₀ s₉

lemma switch_8478559864707290525_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8478559864707290525_concrete_of_code s₀ s₉ →
  Spec A_switch_8478559864707290525 s₀ s₉ := by
  intro h
  simpa [A_switch_8478559864707290525] using h

end

end L1AssetRouter.Common
