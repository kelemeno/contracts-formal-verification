import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_1869195238579639476
import generated.L1AssetRouter.L1AssetRouter.Common.block_6352941606389076905
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.block_8460109867782443930
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.block_4288606231412161876
import generated.L1AssetRouter.L1AssetRouter.mcopy
import generated.L1AssetRouter.L1AssetRouter.Common.block_5043386113996176869
import generated.L1AssetRouter.L1AssetRouter.Common.block_6574497989451738141
import generated.L1AssetRouter.L1AssetRouter.Common.block_5990510130863483261

import generated.L1AssetRouter.L1AssetRouter.Common.switch_2289096099863630418_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_2289096099863630418 (s₀ s₉ : State) : Prop := switch_2289096099863630418_concrete_of_code.1 s₀ s₉

lemma switch_2289096099863630418_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2289096099863630418_concrete_of_code s₀ s₉ →
  Spec A_switch_2289096099863630418 s₀ s₉ := by
  intro h
  simpa [A_switch_2289096099863630418] using h

end

end L1AssetRouter.Common
