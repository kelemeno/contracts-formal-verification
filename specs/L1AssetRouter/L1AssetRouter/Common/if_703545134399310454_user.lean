import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_3084521017962521856
import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset
import generated.L1AssetRouter.L1AssetRouter.Common.block_5208054727264795434

import generated.L1AssetRouter.L1AssetRouter.Common.if_703545134399310454_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_703545134399310454 (s₀ s₉ : State) : Prop := if_703545134399310454_concrete_of_code.1 s₀ s₉

lemma if_703545134399310454_abs_of_concrete {s₀ s₉ : State} :
  Spec if_703545134399310454_concrete_of_code s₀ s₉ →
  Spec A_if_703545134399310454 s₀ s₉ := by
  intro h
  simpa [A_if_703545134399310454] using h

end

end L1AssetRouter.Common
