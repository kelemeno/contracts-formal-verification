import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.revert_forward

import generated.L2AssetRouter.L2AssetRouter.Common.if_7069222774777857031_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_7069222774777857031 (s₀ s₉ : State) : Prop := if_7069222774777857031_concrete_of_code.1 s₀ s₉

lemma if_7069222774777857031_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7069222774777857031_concrete_of_code s₀ s₉ →
  Spec A_if_7069222774777857031 s₀ s₉ := by
  intro h
  simpa [A_if_7069222774777857031] using h

end

end L2AssetRouter.Common
