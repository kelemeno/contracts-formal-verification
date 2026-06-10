import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_fun_bridgehubDepositNonBaseTokenAsset
    (var_request_mpos : Identifier)
    (var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault : Literal)
    (s₀ s₉ : State) : Prop :=
  fun_bridgehubDepositNonBaseTokenAsset_concrete_of_code.1 var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault s₀ s₉

lemma fun_bridgehubDepositNonBaseTokenAsset_abs_of_concrete {s₀ s₉ : State} {var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault} :
  Spec (fun_bridgehubDepositNonBaseTokenAsset_concrete_of_code.1 var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault) s₀ s₉ →
  Spec (A_fun_bridgehubDepositNonBaseTokenAsset var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault) s₀ s₉ := by
  intro h
  simpa [A_fun_bridgehubDepositNonBaseTokenAsset] using h

end

end generated.L1AssetRouter.L1AssetRouter
