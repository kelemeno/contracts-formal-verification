import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_6395570222330567500
import generated.L1AssetRouter.L1AssetRouter.Common.switch_9117052861744899638
import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L1AssetRouter.L1AssetRouter.fun_requireNotPaused
import generated.L1AssetRouter.L1AssetRouter.fun__bridgehubDeposit_inner

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDeposit_inner_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_fun_bridgehubDeposit_inner (var_request_mpos : Identifier) (var_chainId var_originalCaller var__value var_data_offset var_data_length : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_bridgehubDeposit_inner_abs_of_concrete {s₀ s₉ : State} {var_request_mpos var_chainId var_originalCaller var__value var_data_offset var_data_length} :
  Spec (fun_bridgehubDeposit_inner_concrete_of_code.1 var_request_mpos var_chainId var_originalCaller var__value var_data_offset var_data_length) s₀ s₉ →
  Spec (A_fun_bridgehubDeposit_inner var_request_mpos var_chainId var_originalCaller var__value var_data_offset var_data_length) s₀ s₉ := by
  unfold fun_bridgehubDeposit_inner_concrete_of_code A_fun_bridgehubDeposit_inner
  unfold A_fun_bridgehubDeposit_inner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
