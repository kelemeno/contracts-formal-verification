import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_5066914658110926335
import generated.L2AssetRouter.L2AssetRouter.Common.block_762509016437372762

import generated.L2AssetRouter.L2AssetRouter.Common.if_8262361427679300529_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_8262361427679300529 (s₀ s₉ : State) : Prop := sorry

lemma if_8262361427679300529_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8262361427679300529_concrete_of_code s₀ s₉ →
  Spec A_if_8262361427679300529 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
