import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5922704974542936864
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_7014113024450494669

import generated.L1AssetRouter.L1AssetRouter.Common.if_5327636436625673687_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5327636436625673687 (s₀ s₉ : State) : Prop := sorry

lemma if_5327636436625673687_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5327636436625673687_concrete_of_code s₀ s₉ →
  Spec A_if_5327636436625673687 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
