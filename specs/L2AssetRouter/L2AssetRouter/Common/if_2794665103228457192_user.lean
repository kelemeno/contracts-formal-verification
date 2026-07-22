import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_843498061128116258
import generated.L2AssetRouter.L2AssetRouter.Common.block_7877622705106751941

import generated.L2AssetRouter.L2AssetRouter.Common.if_2794665103228457192_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_2794665103228457192 (s₀ s₉ : State) : Prop := sorry

lemma if_2794665103228457192_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2794665103228457192_concrete_of_code s₀ s₉ →
  Spec A_if_2794665103228457192 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
