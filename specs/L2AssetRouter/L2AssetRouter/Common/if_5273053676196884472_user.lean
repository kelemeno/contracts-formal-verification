import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode

import generated.L2AssetRouter.L2AssetRouter.Common.if_5273053676196884472_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_5273053676196884472 (s₀ s₉ : State) : Prop := if_5273053676196884472_concrete_of_code.1 s₀ s₉

lemma if_5273053676196884472_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5273053676196884472_concrete_of_code s₀ s₉ →
  Spec A_if_5273053676196884472 s₀ s₉ := by
  intro h
  simpa [A_if_5273053676196884472] using h

end

end L2AssetRouter.Common
