import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5712827528392086091
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_7387018111745120798

import generated.L1AssetRouter.L1AssetRouter.Common.if_146527745671375149_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_146527745671375149 (s₀ s₉ : State) : Prop := sorry

lemma if_146527745671375149_abs_of_concrete {s₀ s₉ : State} :
  Spec if_146527745671375149_concrete_of_code s₀ s₉ →
  Spec A_if_146527745671375149 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
