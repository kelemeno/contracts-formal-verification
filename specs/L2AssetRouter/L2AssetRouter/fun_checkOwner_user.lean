import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_2101415743686517780
import generated.L2AssetRouter.L2AssetRouter.Common.block_2553657916893711445
import generated.L2AssetRouter.L2AssetRouter.Common.if_8262361427679300529

import generated.L2AssetRouter.L2AssetRouter.fun_checkOwner_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_fun_checkOwner   (s₀ s₉ : State) : Prop := sorry

lemma fun_checkOwner_abs_of_concrete {s₀ s₉ : State}  :
  Spec (fun_checkOwner_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_fun_checkOwner  ) s₀ s₉ := by
  unfold fun_checkOwner_concrete_of_code A_fun_checkOwner
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
