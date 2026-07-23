import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32

import generated.L2AssetRouter.L2AssetRouter.Common.if_6945705467323769142_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_6945705467323769142 (s₀ s₉ : State) : Prop := if_6945705467323769142_concrete_of_code.1 s₀ s₉

lemma if_6945705467323769142_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6945705467323769142_concrete_of_code s₀ s₉ →
  Spec A_if_6945705467323769142 s₀ s₉ := by
  intro h
  simpa [A_if_6945705467323769142] using h

end

end L2AssetRouter.Common
