import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_8188324060275792927
import generated.L2AssetRouter.L2AssetRouter.Common.block_7144817202089613611
import generated.L2AssetRouter.L2AssetRouter.abi_encode_uint256_bytes32_bytes
import generated.L2AssetRouter.L2AssetRouter.Common.block_2145089713075682773
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation

import generated.L2AssetRouter.L2AssetRouter.fun_getDepositCalldata_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_fun_getDepositCalldata (var_1373_mpos : Identifier) (var_assetId var_assetData_mpos : Literal) (s₀ s₉ : State) : Prop := fun_getDepositCalldata_concrete_of_code.1 var_1373_mpos var_assetId var_assetData_mpos s₀ s₉

lemma fun_getDepositCalldata_abs_of_concrete {s₀ s₉ : State} {var_1373_mpos var_assetId var_assetData_mpos} :
  Spec (fun_getDepositCalldata_concrete_of_code.1 var_1373_mpos var_assetId var_assetData_mpos) s₀ s₉ →
  Spec (A_fun_getDepositCalldata var_1373_mpos var_assetId var_assetData_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_getDepositCalldata] using h

end

end generated.L2AssetRouter.L2AssetRouter
