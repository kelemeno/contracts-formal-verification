import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3450160729297863363
import generated.L1AssetRouter.L1AssetRouter.Common.if_1218442921094323335
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_4489986574598841796
import generated.L1AssetRouter.L1AssetRouter.Common.if_3549375524455581443
import generated.L1AssetRouter.L1AssetRouter.Common.if_4257910269798896040
import generated.L1AssetRouter.L1AssetRouter.Common.if_8154557830264771290
import generated.L1AssetRouter.L1AssetRouter.Common.switch_5582855956988081048
import generated.L1AssetRouter.L1AssetRouter.Common.if_8334930945157384518
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory

import generated.L1AssetRouter.L1AssetRouter.fun_transferFundsToNTV_inner_gen


/-
  Formal spec for the Yul translation of L1AssetRouter.transferFundsToNTV.
  Solidity: era-contracts/l1-contracts/contracts/bridge/asset-router/L1AssetRouter.sol
  Function: transferFundsToNTV(bytes32 _assetId, uint256 _amount, address _originalCaller) (lines 409–441).
  Interface: IL1AssetRouter.transferFundsToNTV in same directory.
-/

namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

-- Abstract spec: when the function returns true (var = 1), the NTV balance increase equals the amount.
-- Corresponds to Solidity: require(balanceAfter - balanceBefore == _amount, ...); return true; (L1AssetRouter.sol ~437)
def A_fun_transferFundsToNTV_inner
    (var : Identifier) (var_assetId var_amount var_originalCaller : Literal) (s₀ s₉ : State) : Prop :=
  s₉[var]!! = 1 → s₉["expr_9"]!! - s₉["expr_6"]!! = var_amount

lemma fun_transferFundsToNTV_inner_abs_of_concrete {s₀ s₉ : State} {var var_assetId var_amount var_originalCaller} :
  Spec (fun_transferFundsToNTV_inner_concrete_of_code.1 var var_assetId var_amount var_originalCaller) s₀ s₉ →
  Spec (A_fun_transferFundsToNTV_inner var var_assetId var_amount var_originalCaller) s₀ s₉ := by
  unfold fun_transferFundsToNTV_inner_concrete_of_code A_fun_transferFundsToNTV_inner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete hret
  clr_funargs at hconcrete
  aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
