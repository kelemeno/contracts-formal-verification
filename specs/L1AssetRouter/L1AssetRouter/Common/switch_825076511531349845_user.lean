import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_5144273952670483922
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.Common.if_6076228545724984546

import generated.L1AssetRouter.L1AssetRouter.Common.switch_825076511531349845_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_825076511531349845 (s₀ s₉ : State) : Prop := sorry

lemma switch_825076511531349845_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_825076511531349845_concrete_of_code s₀ s₉ →
  Spec A_switch_825076511531349845 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
