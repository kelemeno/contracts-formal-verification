import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_2308638101162300460
import generated.L1AssetRouter.L1AssetRouter.Common.if_1227481076126767289
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_3425329046457491520_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_3425329046457491520 (s₀ s₉ : State) : Prop := sorry

lemma if_3425329046457491520_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3425329046457491520_concrete_of_code s₀ s₉ →
  Spec A_if_3425329046457491520 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
