import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_1974957643560532488_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_1974957643560532488 (s₀ s₉ : State) : Prop := sorry

lemma if_1974957643560532488_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1974957643560532488_concrete_of_code s₀ s₉ →
  Spec A_if_1974957643560532488 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
