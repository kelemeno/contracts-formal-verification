import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4972084216604715239
import generated.L1AssetRouter.L1AssetRouter.Common.if_7457983452721418043
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_7261898839895920526_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_7261898839895920526 (s₀ s₉ : State) : Prop := sorry

lemma if_7261898839895920526_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7261898839895920526_concrete_of_code s₀ s₉ →
  Spec A_if_7261898839895920526 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
