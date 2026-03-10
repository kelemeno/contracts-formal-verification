import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_13760576345689800

import generated.L1AssetRouter.L1AssetRouter.Common.if_5198757265867716647_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_5198757265867716647 (s₀ s₉ : State) : Prop := sorry

lemma if_5198757265867716647_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5198757265867716647_concrete_of_code s₀ s₉ →
  Spec A_if_5198757265867716647 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
