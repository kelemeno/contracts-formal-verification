import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_1970375284770211925
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_4046858552156044244

import generated.L1AssetRouter.L1AssetRouter.Common.if_5766171955290632522_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5766171955290632522 (s₀ s₉ : State) : Prop :=
  if_5766171955290632522_concrete_of_code.1 s₀ s₉

lemma if_5766171955290632522_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5766171955290632522_concrete_of_code s₀ s₉ →
  Spec A_if_5766171955290632522 s₀ s₉ := by
  intro h
  simpa [A_if_5766171955290632522] using h

end

end L1AssetRouter.Common
