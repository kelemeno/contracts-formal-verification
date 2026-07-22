import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.abi_decode

import generated.L2AssetRouter.L2AssetRouter.Common.if_3845449680979841486_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_if_3845449680979841486 (s₀ s₉ : State) : Prop := sorry

lemma if_3845449680979841486_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3845449680979841486_concrete_of_code s₀ s₉ →
  Spec A_if_3845449680979841486 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
