import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_6234541684501094515
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_7959753185901063261
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable
import generated.L1AssetRouter.L1AssetRouter.fun_ensureTokenRegisteredWithNTV
import generated.L1AssetRouter.L1AssetRouter.Common.if_6857251361693886381
import generated.L1AssetRouter.L1AssetRouter.Common.if_6871170484688093924
import generated.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData

import generated.L1AssetRouter.L1AssetRouter.Common.switch_4068063516829528856_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_4068063516829528856 (s₀ s₉ : State) : Prop := sorry

lemma switch_4068063516829528856_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4068063516829528856_concrete_of_code s₀ s₉ →
  Spec A_switch_4068063516829528856 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
