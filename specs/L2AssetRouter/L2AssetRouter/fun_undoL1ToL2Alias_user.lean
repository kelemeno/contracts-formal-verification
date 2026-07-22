import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_4261849453262820662
import generated.L2AssetRouter.L2AssetRouter.Common.block_8057673836751932015

import generated.L2AssetRouter.L2AssetRouter.fun_undoL1ToL2Alias_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_fun_undoL1ToL2Alias (var_l1Address : Identifier) (var_l2Address : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_undoL1ToL2Alias_abs_of_concrete {s₀ s₉ : State} {var_l1Address var_l2Address} :
  Spec (fun_undoL1ToL2Alias_concrete_of_code.1 var_l1Address var_l2Address) s₀ s₉ →
  Spec (A_fun_undoL1ToL2Alias var_l1Address var_l2Address) s₀ s₉ := by
  unfold fun_undoL1ToL2Alias_concrete_of_code A_fun_undoL1ToL2Alias
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
