import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_1396886289070214715
import generated.L2AssetRouter.L2AssetRouter.update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter
import generated.L2AssetRouter.L2AssetRouter.Common.block_8376260892832200621

import generated.L2AssetRouter.L2AssetRouter.fun_setAssetHandler_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_fun_setAssetHandler  (var_assetId var_assetHandlerAddress : Literal) (s₀ s₉ : State) : Prop := fun_setAssetHandler_concrete_of_code.1 var_assetId var_assetHandlerAddress s₀ s₉

lemma fun_setAssetHandler_abs_of_concrete {s₀ s₉ : State} { var_assetId var_assetHandlerAddress} :
  Spec (fun_setAssetHandler_concrete_of_code.1  var_assetId var_assetHandlerAddress) s₀ s₉ →
  Spec (A_fun_setAssetHandler  var_assetId var_assetHandlerAddress) s₀ s₉ := by
  intro h
  simpa [A_fun_setAssetHandler] using h

end

end generated.L2AssetRouter.L2AssetRouter
