import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset

import generated.L1AssetRouter.L1AssetRouter.Common.switch_3111734635498524533_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_3111734635498524533 (s₀ s₉ : State) : Prop :=
  switch_3111734635498524533_concrete_of_code.1 s₀ s₉

lemma switch_3111734635498524533_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3111734635498524533_concrete_of_code s₀ s₉ →
  Spec A_switch_3111734635498524533 s₀ s₉ := by
  intro h
  simpa [A_switch_3111734635498524533] using h

end

end L1AssetRouter.Common
