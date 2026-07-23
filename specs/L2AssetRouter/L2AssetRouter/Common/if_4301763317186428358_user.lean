import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.fun_transferOwnership

import generated.L2AssetRouter.L2AssetRouter.Common.if_4301763317186428358_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_4301763317186428358 (s₀ s₉ : State) : Prop := if_4301763317186428358_concrete_of_code.1 s₀ s₉

lemma if_4301763317186428358_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4301763317186428358_concrete_of_code s₀ s₉ →
  Spec A_if_4301763317186428358 s₀ s₉ := by
  intro h
  simpa [A_if_4301763317186428358] using h

end

end L2AssetRouter.Common
