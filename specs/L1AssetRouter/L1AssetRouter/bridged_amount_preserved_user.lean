import Clear.ReasoningPrinciple

import specs.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256_user
import specs.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData_user


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def BridgedAmountPreserved
    (amount : Literal)
    (s_custody s_burn_in s_burn_out s_tx_in s_tx_out : State)
    (burn_ret tx_tail : Identifier)
    (remoteReceiver maybeTokenAddress tx_head originalCaller remoteAssetHandler : Literal) : Prop :=
  (s_custody["expr_9"]!!) - (s_custody["expr_6"]!!) = amount ∧
  ∃ s_burn_mid,
    Spec
      (A_abi_encode_uint256_address_address "split_expr_1"
        ((fun_encodeBridgeBurnData_callstate s_burn_in amount remoteReceiver maybeTokenAddress)["split_expr_0"]!!)
        ((fun_encodeBridgeBurnData_callstate s_burn_in amount remoteReceiver maybeTokenAddress)["var_amount"]!!)
        ((fun_encodeBridgeBurnData_callstate s_burn_in amount remoteReceiver maybeTokenAddress)["var_remoteReceiver"]!!)
        ((fun_encodeBridgeBurnData_callstate s_burn_in amount remoteReceiver maybeTokenAddress)["var_maybeTokenAddress"]!!))
      (fun_encodeBridgeBurnData_callstate s_burn_in amount remoteReceiver maybeTokenAddress) s_burn_mid ∧
    ∃ s_burn_alloc,
      Spec
        (A_finalize_allocation
          ((fun_encodeBridgeBurnData_preFinalize_state s_burn_mid)["expr_4966_mpos"]!!)
          ((fun_encodeBridgeBurnData_preFinalize_state s_burn_mid)["_1"]!!))
        (fun_encodeBridgeBurnData_preFinalize_state s_burn_mid) s_burn_alloc ∧
      s_burn_out = fun_encodeBridgeBurnData_return_state s_burn_in s_burn_alloc burn_ret ∧
      A_abi_encode_address_address_uint256 tx_tail tx_head originalCaller remoteAssetHandler amount s_tx_in s_tx_out

theorem bridged_amount_preserved_across_custody_and_encoding
    {amount : Literal}
    {s_custody s_burn_in s_burn_out s_tx_in s_tx_out : State}
    {burn_ret tx_tail : Identifier}
    {remoteReceiver maybeTokenAddress tx_head originalCaller remoteAssetHandler : Literal}
    (hcustody : (s_custody["expr_9"]!!) - (s_custody["expr_6"]!!) = amount)
    (hburn : A_fun_encodeBridgeBurnData burn_ret amount remoteReceiver maybeTokenAddress s_burn_in s_burn_out)
    (htx : A_abi_encode_address_address_uint256 tx_tail tx_head originalCaller remoteAssetHandler amount s_tx_in s_tx_out) :
    BridgedAmountPreserved amount s_custody s_burn_in s_burn_out s_tx_in s_tx_out
      burn_ret tx_tail remoteReceiver maybeTokenAddress tx_head originalCaller remoteAssetHandler := by
  rcases hburn with ⟨s_burn_mid, s_burn_alloc, habi, halloc, hret⟩
  exact ⟨hcustody, s_burn_mid, s_burn_alloc, habi, halloc, hret, htx⟩

end

end generated.L1AssetRouter.L1AssetRouter
