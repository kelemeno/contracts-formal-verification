import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3696855939461667726
import generated.L2AssetRouter.L2AssetRouter.Common.block_357931881184545228
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation

import generated.L2AssetRouter.L2AssetRouter.fun_encodeBridgeBurnData_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_fun_encodeBridgeBurnData (var_mpos : Identifier) (var_amount : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_encodeBridgeBurnData_abs_of_concrete {s₀ s₉ : State} {var_mpos var_amount} :
  Spec (fun_encodeBridgeBurnData_concrete_of_code.1 var_mpos var_amount) s₀ s₉ →
  Spec (A_fun_encodeBridgeBurnData var_mpos var_amount) s₀ s₉ := by
  unfold fun_encodeBridgeBurnData_concrete_of_code A_fun_encodeBridgeBurnData
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
