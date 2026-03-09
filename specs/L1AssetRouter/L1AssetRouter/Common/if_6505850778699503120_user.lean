import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3601467568867417424
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_1117783195986662844

import generated.L1AssetRouter.L1AssetRouter.Common.if_6505850778699503120_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_6505850778699503120 (s₀ s₉ : State) : Prop := sorry

lemma if_6505850778699503120_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6505850778699503120_concrete_of_code s₀ s₉ →
  Spec A_if_6505850778699503120 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
