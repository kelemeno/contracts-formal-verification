import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32

import generated.L2AssetRouter.L2AssetRouter.Common.if_1068904302988658311_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_1068904302988658311 (s₀ s₉ : State) : Prop := if_1068904302988658311_concrete_of_code.1 s₀ s₉

lemma if_1068904302988658311_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1068904302988658311_concrete_of_code s₀ s₉ →
  Spec A_if_1068904302988658311 s₀ s₉ := by
  intro h
  simpa [A_if_1068904302988658311] using h

end

end L2AssetRouter.Common
