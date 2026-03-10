import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_8559227413688637467
import generated.L1AssetRouter.L1AssetRouter.Common.if_5042156693723988981
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_1466129081489322116
import generated.L1AssetRouter.L1AssetRouter.Common.switch_6544409437594169382
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes

import generated.L1AssetRouter.L1AssetRouter.fun_getDepositCalldata_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_fun_getDepositCalldata
    (var_1083_mpos : Identifier) (var_sender var_assetId var_assetData_mpos : Literal)
    (s₀ s₉ : State) : Prop :=
  fun_getDepositCalldata_concrete_of_code.1 var_1083_mpos var_sender var_assetId var_assetData_mpos s₀ s₉

lemma fun_getDepositCalldata_abs_of_concrete {s₀ s₉ : State} {var_1083_mpos var_sender var_assetId var_assetData_mpos} :
  Spec (fun_getDepositCalldata_concrete_of_code.1 var_1083_mpos var_sender var_assetId var_assetData_mpos) s₀ s₉ →
  Spec (A_fun_getDepositCalldata var_1083_mpos var_sender var_assetId var_assetData_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_getDepositCalldata] using h

end

end generated.L1AssetRouter.L1AssetRouter
