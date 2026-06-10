import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_5066914658110926335
import generated.L1AssetRouter.L1AssetRouter.Common.block_762509016437372762

import generated.L1AssetRouter.L1AssetRouter.Common.if_8262361427679300529_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_8262361427679300529 (s₀ s₉ : State) : Prop := if_8262361427679300529_concrete_of_code.1 s₀ s₉

lemma if_8262361427679300529_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8262361427679300529_concrete_of_code s₀ s₉ →
  Spec A_if_8262361427679300529 s₀ s₉ := by
  intro h
  simpa [A_if_8262361427679300529] using h

end

end L1AssetRouter.Common
