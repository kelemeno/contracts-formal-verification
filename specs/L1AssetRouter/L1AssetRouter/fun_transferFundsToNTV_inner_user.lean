import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_1094181428675153396
import generated.L1AssetRouter.L1AssetRouter.Common.block_4062193457366218320
import generated.L1AssetRouter.L1AssetRouter.Common.block_443363902230444682
import generated.L1AssetRouter.L1AssetRouter.Common.if_8559227413688637467
import generated.L1AssetRouter.L1AssetRouter.Common.if_5042156693723988981
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_4489986574598841796
import generated.L1AssetRouter.L1AssetRouter.Common.if_3549375524455581443
import generated.L1AssetRouter.L1AssetRouter.Common.block_1822537150739106069
import generated.L1AssetRouter.L1AssetRouter.Common.block_7479434513918279295
import generated.L1AssetRouter.L1AssetRouter.Common.block_7592739123798637884
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address
import generated.L1AssetRouter.L1AssetRouter.Common.if_3158875210877696577
import generated.L1AssetRouter.L1AssetRouter.Common.if_5327636436625673687
import generated.L1AssetRouter.L1AssetRouter.Common.switch_8478559864707290525
import generated.L1AssetRouter.L1AssetRouter.Common.if_2082893542340508167
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

  The key custody invariant: when var = 1, the final balance-check block
  (if_2082893542340508167, which contains
     diff := sub(expr_9, expr_6)            -- balanceAfter - balanceBefore
     require(diff == var_amount); var := 1; leave)
  did NOT fall through normally — control left it via `leave`, the control-flow
  witness that the custody guard `require(balanceAfter - balanceBefore == _amount)`
  passed. Falling through that block forces `var := 0`.
-/

namespace generated.L1AssetRouter.L1AssetRouter

section

set_option maxHeartbeats 800000

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

-- Abstract spec: custody-side amount preservation.
-- When the function returns 1, the final balance-difference check block did NOT
-- fall through (it is not an Ok state): control jumped out via `leave`, which is
-- the control-flow witness of the guard
--   require(balanceAfter - balanceBefore == _amount)  [diff := sub(expr_9, expr_6)]
-- passing and the function returning `true`. Falling through always sets var := 0.
def A_fun_transferFundsToNTV_inner
    (var : Identifier) (var_assetId var_amount var_originalCaller : Literal) (s₀ s₉ : State) : Prop :=
  -- There exists an intermediate state entering the final check block
  -- (if_2082893542340508167) and a resulting state from that block, satisfying its spec.
  ∃ s_check_in s_check_out,
    Spec A_if_2082893542340508167 s_check_in s_check_out ∧
    -- When the function returns 1, the final check block did NOT fall through
    -- normally (it is not an Ok state): control jumped out via `leave`, i.e. the
    -- balance-difference guard `require(balanceAfter - balanceBefore == _amount)`
    -- passed and the function returned `true`. (Falling through always sets var := 0.)
    (s₉[var]!! = 1 → ¬ isOk s_check_out)

-- Note: the deeper custody fact (s₉[var]!! = 1 →
--   the observed balance increase `diff = expr_9 - expr_6` equals var_amount) lives
-- inside A_if_2082893542340508167; that abstract spec is currently a thin-wrapper
-- (definitionally the concrete block) in this tree, so the deeper equality is not yet
-- exposed in extractable abstract form. What we do establish is that a successful
-- return (var = 1) is only possible when the final check block jumps out (`leave`)
-- rather than falling through, which is the control-flow witness of the guard passing.

lemma fun_transferFundsToNTV_inner_abs_of_concrete {s₀ s₉ : State} {var var_assetId var_amount var_originalCaller} :
  Spec (fun_transferFundsToNTV_inner_concrete_of_code.1 var var_assetId var_amount var_originalCaller) s₀ s₉ →
  Spec (A_fun_transferFundsToNTV_inner var var_assetId var_amount var_originalCaller) s₀ s₉ := by
  unfold fun_transferFundsToNTV_inner_concrete_of_code A_fun_transferFundsToNTV_inner
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  rcases hconcrete with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ss_out, hspec, heq⟩
  refine ⟨_, ss_out, hspec, ?_⟩
  intro hvar
  rcases ss_out with ⟨e, st⟩ | jc | _
  · -- ss_out is Ok: then s₉ assigns var ↦ 0, contradicting hvar = 1
    exfalso
    rw [← heq] at hvar
    simp only [State.reviveJump] at hvar
    simp only [State.lookup!, Finmap.lookup_insert, Option.get!] at hvar
    exact absurd hvar (by decide)
  · -- ss_out is a Checkpoint: not Ok
    simp [State.isOk]
  · -- ss_out is OutOfFuel: not Ok
    simp [State.isOk]

end

end generated.L1AssetRouter.L1AssetRouter
