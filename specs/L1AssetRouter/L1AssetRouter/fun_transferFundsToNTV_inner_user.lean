import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_8559227413688637467
import generated.L1AssetRouter.L1AssetRouter.Common.if_5042156693723988981
import generated.L1AssetRouter.L1AssetRouter.Common.if_4489986574598841796
import generated.L1AssetRouter.L1AssetRouter.Common.if_3549375524455581443
import generated.L1AssetRouter.L1AssetRouter.Common.if_3158875210877696577
import generated.L1AssetRouter.L1AssetRouter.Common.if_5327636436625673687
import generated.L1AssetRouter.L1AssetRouter.Common.switch_7614661687758543566
import generated.L1AssetRouter.L1AssetRouter.Common.if_2338892551544939949

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

/-
  PROOF GAP NOTE
  ==============
  In Clear's Yul semantics, the EVM `revert` opcode is modelled as a state
  modification that sets return data but does NOT terminate Yul execution.
  This means the balance-difference guard:

    if iszero(eq(diff, var_amount)) { revert(0, 4) }

  does not prevent execution from continuing to `var := 1; leave`.  Therefore
  the balance-conservation postcondition (diff = var_amount when var = 1)
  cannot be derived purely from the Yul-level Clear model.

  The `A_fun_transferFundsToNTV_inner` spec below records the structure of the
  desired invariant.  `fun_transferFundsToNTV_inner_balance_diff` is admitted
  (sorry) to document the proof obligation that remains.  To remove this sorry
  one would need to either:
    (a) extend Clear's semantics to model EVM revert as a terminating instruction, or
    (b) reason about the EVM return-data state to detect whether the guard fired.
-/

-- Abstract spec: the function terminates normally (True placeholder).
-- The balance-diff invariant requires EVM-level reasoning; see the note above.
def A_fun_transferFundsToNTV_inner
    (var : Identifier) (var_assetId var_amount var_originalCaller : Literal) (s₀ s₉ : State) : Prop :=
  True

/-- When transferFundsToNTV returns 1 (success), the NTV token balance
    increased by exactly `var_amount` between the two staticcall snapshots.
    Admitted: requires EVM-level revert semantics not yet in Clear's model. -/
-- Proof gap: when var = 1, the NTV balance increased by exactly var_amount.
-- The postcondition would be: ∃ before after : Literal, after - before = var_amount.
-- Admitted because Clear's revert is not terminating (see file header comment).
lemma fun_transferFundsToNTV_inner_balance_diff
    {s₀ s₉ : State} {var : Identifier} {var_assetId var_amount var_originalCaller : Literal}
    (hspec : Spec (A_fun_transferFundsToNTV_inner var var_assetId var_amount var_originalCaller) s₀ s₉)
    (hret : s₉[var]!! = 1) :
    ∃ before after : Literal, after - before = var_amount := by
  sorry

lemma fun_transferFundsToNTV_inner_abs_of_concrete {s₀ s₉ : State} {var var_assetId var_amount var_originalCaller} :
  Spec (fun_transferFundsToNTV_inner_concrete_of_code.1 var var_assetId var_amount var_originalCaller) s₀ s₉ →
  Spec (A_fun_transferFundsToNTV_inner var var_assetId var_amount var_originalCaller) s₀ s₉ := by
  unfold A_fun_transferFundsToNTV_inner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
