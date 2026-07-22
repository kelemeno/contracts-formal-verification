import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3782755365138259821
import generated.L2AssetRouter.L2AssetRouter.Common.block_2405270268964189352

import generated.L2AssetRouter.L2AssetRouter.Common.if_4012421819531509095_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_4012421819531509095 (s₀ s₉ : State) : Prop := sorry

lemma if_4012421819531509095_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4012421819531509095_concrete_of_code s₀ s₉ →
  Spec A_if_4012421819531509095 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
