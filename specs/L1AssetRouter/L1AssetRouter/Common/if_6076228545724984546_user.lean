import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_1519765272233310974

import generated.L1AssetRouter.L1AssetRouter.Common.if_6076228545724984546_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_6076228545724984546 (s₀ s₉ : State) : Prop := sorry

lemma if_6076228545724984546_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6076228545724984546_concrete_of_code s₀ s₉ →
  Spec A_if_6076228545724984546 s₀ s₉ := by
  sorry

end

end L1AssetRouter.Common
