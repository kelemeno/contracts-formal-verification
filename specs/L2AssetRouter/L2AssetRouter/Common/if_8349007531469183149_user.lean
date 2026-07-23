import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3782755365138259821
import generated.L2AssetRouter.L2AssetRouter.Common.block_2405270268964189352

import generated.L2AssetRouter.L2AssetRouter.Common.if_8349007531469183149_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_8349007531469183149 (s₀ s₉ : State) : Prop := if_8349007531469183149_concrete_of_code.1 s₀ s₉

lemma if_8349007531469183149_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8349007531469183149_concrete_of_code s₀ s₉ →
  Spec A_if_8349007531469183149 s₀ s₉ := by
  intro h
  simpa [A_if_8349007531469183149] using h

end

end L2AssetRouter.Common
