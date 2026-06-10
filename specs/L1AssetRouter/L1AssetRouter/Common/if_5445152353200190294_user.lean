import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_4070886617372402401
import generated.L1AssetRouter.L1AssetRouter.Common.block_5909921818141361415
import generated.L1AssetRouter.L1AssetRouter.Common.if_4123428495707567447
import generated.L1AssetRouter.L1AssetRouter.Common.if_5766171955290632522
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.Common.if_5445152353200190294_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5445152353200190294 (s₀ s₉ : State) : Prop := if_5445152353200190294_concrete_of_code.1 s₀ s₉

lemma if_5445152353200190294_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5445152353200190294_concrete_of_code s₀ s₉ →
  Spec A_if_5445152353200190294 s₀ s₉ := by
  intro h
  simpa [A_if_5445152353200190294] using h

end

end L1AssetRouter.Common
