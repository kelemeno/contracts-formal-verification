import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset

import generated.L1AssetRouter.L1AssetRouter.Common.if_919922969513075000_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_919922969513075000 (s₀ s₉ : State) : Prop := sorry

lemma if_919922969513075000_abs_of_concrete {s₀ s₉ : State} :
  Spec if_919922969513075000_concrete_of_code s₀ s₉ →
  Spec A_if_919922969513075000 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
