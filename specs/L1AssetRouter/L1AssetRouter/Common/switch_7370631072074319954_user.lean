import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset

import generated.L1AssetRouter.L1AssetRouter.Common.switch_7370631072074319954_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_7370631072074319954 (s₀ s₉ : State) : Prop := sorry

lemma switch_7370631072074319954_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7370631072074319954_concrete_of_code s₀ s₉ →
  Spec A_switch_7370631072074319954 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
