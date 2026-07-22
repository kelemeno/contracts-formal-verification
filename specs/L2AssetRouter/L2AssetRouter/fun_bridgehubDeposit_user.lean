import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L2AssetRouter.L2AssetRouter.fun_requireNotPaused
import generated.L2AssetRouter.L2AssetRouter.fun_bridgehubDeposit_inner

import generated.L2AssetRouter.L2AssetRouter.fun_bridgehubDeposit_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_fun_bridgehubDeposit (var_request_mpos : Identifier) (var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_bridgehubDeposit_abs_of_concrete {s₀ s₉ : State} {var_request_mpos var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault} :
  Spec (fun_bridgehubDeposit_concrete_of_code.1 var_request_mpos var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault) s₀ s₉ →
  Spec (A_fun_bridgehubDeposit var_request_mpos var_chainId var_originalCaller var_value var_data_offset var_data_length var_nativeTokenVault) s₀ s₉ := by
  unfold fun_bridgehubDeposit_concrete_of_code A_fun_bridgehubDeposit
  sorry

end

end generated.L2AssetRouter.L2AssetRouter
