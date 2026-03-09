import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_8784080788282594326
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_3680740834951988335
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.switch_2492635462891078030_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_2492635462891078030 (s₀ s₉ : State) : Prop := sorry

lemma switch_2492635462891078030_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2492635462891078030_concrete_of_code s₀ s₉ →
  Spec A_switch_2492635462891078030 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
