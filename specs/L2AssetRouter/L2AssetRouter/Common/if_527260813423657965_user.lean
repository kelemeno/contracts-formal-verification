import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_890060666481180239
import generated.L2AssetRouter.L2AssetRouter.Common.block_1564038066900963958

import generated.L2AssetRouter.L2AssetRouter.Common.if_527260813423657965_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_527260813423657965 (s₀ s₉ : State) : Prop := if_527260813423657965_concrete_of_code.1 s₀ s₉

lemma if_527260813423657965_abs_of_concrete {s₀ s₉ : State} :
  Spec if_527260813423657965_concrete_of_code s₀ s₉ →
  Spec A_if_527260813423657965 s₀ s₉ := by
  intro h
  simpa [A_if_527260813423657965] using h

end

end L2AssetRouter.Common
