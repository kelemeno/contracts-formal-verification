import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.panic_error_0x11

import generated.L2AssetRouter.L2AssetRouter.Common.if_9101434560028777380_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_9101434560028777380 (s₀ s₉ : State) : Prop := sorry

lemma if_9101434560028777380_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9101434560028777380_concrete_of_code s₀ s₉ →
  Spec A_if_9101434560028777380 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
