import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3154717291655483374
import generated.L1AssetRouter.L1AssetRouter.Common.if_1213823114410652249
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_3425329046457491520
import generated.L1AssetRouter.L1AssetRouter.Common.if_6347281329581904638

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5582855956988081048_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_5582855956988081048 (s₀ s₉ : State) : Prop := sorry

lemma switch_5582855956988081048_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5582855956988081048_concrete_of_code s₀ s₉ →
  Spec A_switch_5582855956988081048 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
