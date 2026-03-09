import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_2061709964753258792
import generated.L1AssetRouter.L1AssetRouter.Common.if_7457983452721418043
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_9182385200371437658_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_9182385200371437658 (s₀ s₉ : State) : Prop := sorry

lemma if_9182385200371437658_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9182385200371437658_concrete_of_code s₀ s₉ →
  Spec A_if_9182385200371437658 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
