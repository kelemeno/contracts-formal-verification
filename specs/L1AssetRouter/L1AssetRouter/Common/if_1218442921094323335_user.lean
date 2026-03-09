import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5144880483535547481
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_1218442921094323335_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1218442921094323335 (s₀ s₉ : State) : Prop := sorry

lemma if_1218442921094323335_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1218442921094323335_concrete_of_code s₀ s₉ →
  Spec A_if_1218442921094323335 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
