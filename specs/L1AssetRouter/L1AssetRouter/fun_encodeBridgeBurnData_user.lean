import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_address_address
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_fun_encodeBridgeBurnData (var_4959_mpos : Identifier)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) (s₀ s₉ : State) : Prop :=
  fun_encodeBridgeBurnData_concrete_of_code.1 var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress s₀ s₉

lemma fun_encodeBridgeBurnData_abs_of_concrete {s₀ s₉ : State} {var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress} :
  Spec (fun_encodeBridgeBurnData_concrete_of_code.1 var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress) s₀ s₉ →
  Spec (A_fun_encodeBridgeBurnData var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress) s₀ s₉ := by
  intro h
  simpa [A_fun_encodeBridgeBurnData] using h

end

end generated.L1AssetRouter.L1AssetRouter
