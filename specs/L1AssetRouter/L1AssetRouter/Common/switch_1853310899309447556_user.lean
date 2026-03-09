import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset

import generated.L1AssetRouter.L1AssetRouter.Common.switch_1853310899309447556_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_1853310899309447556 (s₀ s₉ : State) : Prop := sorry

lemma switch_1853310899309447556_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1853310899309447556_concrete_of_code s₀ s₉ →
  Spec A_switch_1853310899309447556 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
