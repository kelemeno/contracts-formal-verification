import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3782755365138259821
import generated.L2AssetRouter.L2AssetRouter.Common.block_2405270268964189352

import generated.L2AssetRouter.L2AssetRouter.Common.if_6167752411855890517_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_if_6167752411855890517 (s₀ s₉ : State) : Prop := sorry

lemma if_6167752411855890517_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6167752411855890517_concrete_of_code s₀ s₉ →
  Spec A_if_6167752411855890517 s₀ s₉ := by
  sorry

end

end L2AssetRouter.Common
