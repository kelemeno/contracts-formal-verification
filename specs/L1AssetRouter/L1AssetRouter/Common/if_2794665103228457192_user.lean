import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_843498061128116258
import generated.L1AssetRouter.L1AssetRouter.Common.block_7877622705106751941

import generated.L1AssetRouter.L1AssetRouter.Common.if_2794665103228457192_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_2794665103228457192 (s₀ s₉ : State) : Prop := if_2794665103228457192_concrete_of_code.1 s₀ s₉

lemma if_2794665103228457192_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2794665103228457192_concrete_of_code s₀ s₉ →
  Spec A_if_2794665103228457192 s₀ s₉ := by
  intro h
  simpa [A_if_2794665103228457192] using h

end

end L1AssetRouter.Common
