import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4901459930403710601

import generated.L2AssetRouter.L2AssetRouter.Common.if_7506617587990959785_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_7506617587990959785 (s₀ s₉ : State) : Prop := sorry

lemma if_7506617587990959785_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7506617587990959785_concrete_of_code s₀ s₉ →
  Spec A_if_7506617587990959785 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
