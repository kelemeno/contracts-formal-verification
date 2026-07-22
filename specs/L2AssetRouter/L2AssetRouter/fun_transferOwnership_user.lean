import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_8262768811093514272
import generated.L2AssetRouter.L2AssetRouter.Common.block_7787473196838721966
import generated.L2AssetRouter.L2AssetRouter.Common.block_6732273366845292413
import generated.L2AssetRouter.L2AssetRouter.Common.block_4544268925825994618

import generated.L2AssetRouter.L2AssetRouter.fun_transferOwnership_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_fun_transferOwnership  (var_newOwner : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_transferOwnership_abs_of_concrete {s₀ s₉ : State} { var_newOwner} :
  Spec (fun_transferOwnership_concrete_of_code.1  var_newOwner) s₀ s₉ →
  Spec (A_fun_transferOwnership  var_newOwner) s₀ s₉ := by
  unfold fun_transferOwnership_concrete_of_code A_fun_transferOwnership
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
