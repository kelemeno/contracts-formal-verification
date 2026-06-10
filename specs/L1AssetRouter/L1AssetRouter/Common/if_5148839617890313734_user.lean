import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_5878814341832663592
import generated.L1AssetRouter.L1AssetRouter.Common.block_5170046727095826309

import generated.L1AssetRouter.L1AssetRouter.Common.if_5148839617890313734_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_5148839617890313734 (s₀ s₉ : State) : Prop := if_5148839617890313734_concrete_of_code.1 s₀ s₉

lemma if_5148839617890313734_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5148839617890313734_concrete_of_code s₀ s₉ →
  Spec A_if_5148839617890313734 s₀ s₉ := by
  intro h
  simpa [A_if_5148839617890313734] using h

end

end L1AssetRouter.Common
