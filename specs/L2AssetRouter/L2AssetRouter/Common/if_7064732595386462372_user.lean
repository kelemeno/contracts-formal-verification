import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_5603149534314911961
import generated.L2AssetRouter.L2AssetRouter.Common.block_8963643643639495716

import generated.L2AssetRouter.L2AssetRouter.Common.if_7064732595386462372_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_7064732595386462372 (s₀ s₉ : State) : Prop := sorry

lemma if_7064732595386462372_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7064732595386462372_concrete_of_code s₀ s₉ →
  Spec A_if_7064732595386462372 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
