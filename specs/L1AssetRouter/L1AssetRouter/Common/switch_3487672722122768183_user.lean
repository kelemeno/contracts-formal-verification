import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.switch_3487672722122768183_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_switch_3487672722122768183 (s₀ s₉ : State) : Prop := sorry

lemma switch_3487672722122768183_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3487672722122768183_concrete_of_code s₀ s₉ →
  Spec A_switch_3487672722122768183 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
