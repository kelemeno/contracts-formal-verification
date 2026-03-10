import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4123428495707567447
import generated.L1AssetRouter.L1AssetRouter.Common.if_5766171955290632522
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_1466129081489322116_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_1466129081489322116 (s₀ s₉ : State) : Prop := sorry

lemma if_1466129081489322116_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1466129081489322116_concrete_of_code s₀ s₉ →
  Spec A_if_1466129081489322116 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
