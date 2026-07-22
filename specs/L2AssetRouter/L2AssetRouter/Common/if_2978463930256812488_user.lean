import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_8767191686854038847
import generated.L2AssetRouter.L2AssetRouter.Common.block_4431226694517804810

import generated.L2AssetRouter.L2AssetRouter.Common.if_2978463930256812488_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_2978463930256812488 (s₀ s₉ : State) : Prop := sorry

lemma if_2978463930256812488_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2978463930256812488_concrete_of_code s₀ s₉ →
  Spec A_if_2978463930256812488 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
