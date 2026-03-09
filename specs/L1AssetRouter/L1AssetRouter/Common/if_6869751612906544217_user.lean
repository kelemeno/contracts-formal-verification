import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5144880483535547481
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_494729114087865584

import generated.L1AssetRouter.L1AssetRouter.Common.if_6869751612906544217_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_6869751612906544217 (s₀ s₉ : State) : Prop := sorry

lemma if_6869751612906544217_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6869751612906544217_concrete_of_code s₀ s₉ →
  Spec A_if_6869751612906544217 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
