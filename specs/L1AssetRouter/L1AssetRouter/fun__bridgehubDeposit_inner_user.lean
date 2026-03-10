import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset

import generated.L1AssetRouter.L1AssetRouter.Common.if_4118729959615125189
import generated.L1AssetRouter.L1AssetRouter.Common.switch_3111734635498524533

import generated.L1AssetRouter.L1AssetRouter.fun__bridgehubDeposit_inner_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_fun__bridgehubDeposit_inner (var_request_mpos : Identifier) (var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault : Literal) (s₀ s₉ : State) : Prop := True

lemma fun__bridgehubDeposit_inner_abs_of_concrete {s₀ s₉ : State} {var_request_mpos var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault} :
  Spec (fun__bridgehubDeposit_inner_concrete_of_code.1 var_request_mpos var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault) s₀ s₉ →
  Spec (A_fun__bridgehubDeposit_inner var_request_mpos var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault) s₀ s₉ := by
  unfold fun__bridgehubDeposit_inner_concrete_of_code A_fun__bridgehubDeposit_inner
  unfold A_fun__bridgehubDeposit_inner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
