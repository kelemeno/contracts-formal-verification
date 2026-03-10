import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_8559227413688637467
import generated.L1AssetRouter.L1AssetRouter.Common.if_2159961819437569804
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_4489986574598841796
import generated.L1AssetRouter.L1AssetRouter.Common.if_3549375524455581443
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_5821215989349451585
import generated.L1AssetRouter.L1AssetRouter.Common.if_8154557830264771290
import generated.L1AssetRouter.L1AssetRouter.Common.switch_7725928570327963402
import generated.L1AssetRouter.L1AssetRouter.Common.if_5678193105413593853
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory

import generated.L1AssetRouter.L1AssetRouter.fun_transferFundsToNTV_inner_gen


/-
  Formal spec for the Yul translation of L1AssetRouter.transferFundsToNTV.
  Solidity: era-contracts/l1-contracts/contracts/bridge/asset-router/L1AssetRouter.sol
  Function: transferFundsToNTV(bytes32 _assetId, uint256 _amount, address _originalCaller) (lines 409–441).
  Interface: IL1AssetRouter.transferFundsToNTV in same directory.

  Semantic summary:
  - The function reads the NTV address from storage, resolves the token via staticcall,
    checks allowances, performs a safeTransferFrom, then verifies that
    balanceAfter - balanceBefore == _amount.
  - If the balance check passes, it returns var = 1 (success) via leave.
  - If the check fails, it reverts.
  - If the token is zero/one or the transfer is not needed, it returns var = 0.

  The key custody invariant: when var = 1, there exist intermediate balance
  observations (expr_6 = balanceBefore, expr_9 = balanceAfter) such that
  balanceAfter - balanceBefore = var_amount.
-/

namespace generated.L1AssetRouter.L1AssetRouter

section

set_option maxHeartbeats 800000

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

-- Abstract spec: custody-side amount preservation.
-- When the function returns 1, there exist intermediate balance observations
-- (from staticcalls to the NTV contract) whose difference equals var_amount.
-- This is the Yul-level rendering of Solidity's
--   require(balanceAfter - balanceBefore == _amount, "..."); return true;
def A_fun_transferFundsToNTV_inner
    (var : Identifier) (var_assetId var_amount var_originalCaller : Literal) (s₀ s₉ : State) : Prop :=
  -- There exists an intermediate state entering the final check block (if_5678193105413593853)
  -- and a resulting state from that block, satisfying its spec.
  ∃ s_check_in s_check_out,
    Spec A_if_5678193105413593853 s_check_in s_check_out ∧
    -- The amount parameter was correctly threaded through the call chain
    s_check_in["var_amount"]!! = var_amount ∧
    -- When the function returns 1, the check block was entered and left successfully,
    -- which means the balance-difference guard passed.
    (s₉[var]!! = 1 → s_check_in["var_weCanTransfer"]!! ≠ 0 ∧ isLeave s_check_out)

-- The key derived fact (from A_if_5678193105413593853 + the above):
-- s₉[var]!! = 1 →
--   (s_check_in["expr_9"]!!) - (s_check_in["expr_6"]!!) = var_amount
-- i.e., the observed balance increase equals the requested amount.
--
-- This is currently only a comment because A_if_5678193105413593853 is a
-- trivial (True) auto-generated spec and does not yet carry the balance
-- information.  The lemma below records the shape of what needs to be proved
-- once A_if_5678193105413593853 is strengthened to capture the Yul-level
-- semantics of the balance-difference guard:
--
--   if (balanceAfter - balanceBefore != _amount) { revert }
--
-- To lift this sorry: write a hand-crafted spec for if_5678193105413593853 in
-- specs/L1AssetRouter/L1AssetRouter/Common/if_5678193105413593853_user.lean
-- that asserts:
--   isLeave s₉ → s₀["expr_9"]!! - s₀["expr_6"]!! = s₀["var_amount"]!!
-- Then replace sorry below with the extraction from hspec.

/-- When transferFundsToNTV returns 1 (success), the NTV token balance
    increased by exactly `var_amount` between the two staticcall snapshots.
    `expr_6` and `expr_9` are the Yul-level temporaries for balanceBefore and
    balanceAfter respectively.
    This lemma is admitted until A_if_5678193105413593853 carries the
    balance postcondition. -/
lemma fun_transferFundsToNTV_inner_balance_diff
    {s₀ s₉ : State} {var : Identifier} {var_assetId var_amount var_originalCaller : Literal}
    (hspec : Spec (A_fun_transferFundsToNTV_inner var var_assetId var_amount var_originalCaller) s₀ s₉)
    (hret : s₉[var]!! = 1) :
    ∃ s_check_in : State,
      s_check_in["expr_9"]!! - s_check_in["expr_6"]!! = var_amount := by
  -- The balance-diff information lives in s_check_in["expr_9"]!! - s_check_in["expr_6"]!!
  -- once A_if_5678193105413593853 is strengthened.  For now we admit this.
  sorry

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
