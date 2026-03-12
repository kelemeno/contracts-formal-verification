import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable
import generated.L1AssetRouter.L1AssetRouter.fun_ensureTokenRegisteredWithNTV
import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId
import generated.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_memory_ptr_fromMemory
import generated.L1AssetRouter.L1AssetRouter.mcopy
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256
import generated.L1AssetRouter.L1AssetRouter.fun_getDepositCalldata
import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947

import specs.L1AssetRouter.L1AssetRouter.bridged_amount_preserved_user

import generated.L1AssetRouter.L1AssetRouter.Common.if_4177257432569412076
import generated.L1AssetRouter.L1AssetRouter.Common.switch_4675297000597642223
import generated.L1AssetRouter.L1AssetRouter.Common.if_510303534436936689
import generated.L1AssetRouter.L1AssetRouter.Common.if_769693910280520188
import generated.L1AssetRouter.L1AssetRouter.Common.if_5425314748063330981
import generated.L1AssetRouter.L1AssetRouter.Common.if_7118975047039834028
import generated.L1AssetRouter.L1AssetRouter.Common.if_5903850729805010006
import generated.L1AssetRouter.L1AssetRouter.Common.if_6182723117196027006
import generated.L1AssetRouter.L1AssetRouter.Common.switch_9186551833083700771

import generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_fun_bridgehubDepositNonBaseTokenAsset
    (var_request_mpos : Identifier)
    (var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault : Literal)
    (s₀ s₉ : State) : Prop :=
  fun_bridgehubDepositNonBaseTokenAsset_concrete_of_code.1
    var_request_mpos var_chainId var_originalCaller var_value var__data_offset
    var_data_1714_length var_nativeTokenVault s₀ s₉

lemma fun_bridgehubDepositNonBaseTokenAsset_abs_of_concrete {s₀ s₉ : State} {var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault} :
  Spec (fun_bridgehubDepositNonBaseTokenAsset_concrete_of_code.1 var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault) s₀ s₉ →
  Spec (A_fun_bridgehubDepositNonBaseTokenAsset var_request_mpos var_chainId var_originalCaller var_value var__data_offset var_data_1714_length var_nativeTokenVault) s₀ s₉ := by
  intro h
  simpa [A_fun_bridgehubDepositNonBaseTokenAsset] using h

theorem bridgehubDepositNonBaseTokenAsset_preserves_bridged_amount
    {amount : Literal}
    {s_custody s_burn_in s_burn_out s_tx_in s_tx_out : State}
    {burn_ret tx_tail : Identifier}
    {remoteReceiver maybeTokenAddress tx_head originalCaller remoteAssetHandler : Literal}
    (hcustody : (s_custody["expr_9"]!!) - (s_custody["expr_6"]!!) = amount)
    (hburn : A_fun_encodeBridgeBurnData burn_ret amount remoteReceiver maybeTokenAddress s_burn_in s_burn_out)
    (htx : A_abi_encode_address_address_uint256 tx_tail tx_head originalCaller remoteAssetHandler amount s_tx_in s_tx_out) :
    BridgedAmountPreserved amount s_custody s_burn_in s_burn_out s_tx_in s_tx_out
      burn_ret tx_tail remoteReceiver maybeTokenAddress tx_head originalCaller remoteAssetHandler :=
  bridged_amount_preserved_across_custody_and_encoding hcustody hburn htx

end

end generated.L1AssetRouter.L1AssetRouter
