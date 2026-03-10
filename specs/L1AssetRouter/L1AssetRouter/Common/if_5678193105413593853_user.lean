import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4192851695953284299
import generated.L1AssetRouter.L1AssetRouter.Common.if_5565014839478708744
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256
import generated.L1AssetRouter.L1AssetRouter.Common.switch_4762451955261439273
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.Common.if_2639820713918449020
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_7658994005994128507
import generated.L1AssetRouter.L1AssetRouter.Common.if_8278993253547397643
import generated.L1AssetRouter.L1AssetRouter.Common.if_146527745671375149
import generated.L1AssetRouter.L1AssetRouter.Common.if_4281470425710111854
import generated.L1AssetRouter.L1AssetRouter.Common.if_3311041079225076058

import generated.L1AssetRouter.L1AssetRouter.Common.if_5678193105413593853_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

/-
  Formal spec for the `if var_weCanTransfer { ... }` block inside
  `fun_transferFundsToNTV_inner` (Yul lines 2096–2119 in L1AssetRouter.yul).

  When `var_weCanTransfer ≠ 0`, the block:
    1. staticcalls balanceOf → expr_6  (balanceBefore)
    2. calls safeTransferFrom
    3. staticcalls balanceOf → expr_9  (balanceAfter)
    4. diff := sub(expr_9, expr_6)
    5. if gt(diff, expr_9) { revert }             -- overflow guard
    6. if iszero(eq(diff, var_amount)) { revert } -- balance diff guard
    7. var := 1; leave                            -- success

  KEY POSTCONDITION (when isLeave s₉):
    - s₉["var"]!!  = 1
    - s₉["diff"]!! = s₀["var_amount"]!!
    - s₉["diff"]!! = s₉["expr_9"]!! - s₉["expr_6"]!!
    - ¬(s₉["expr_9"]!! < s₉["expr_6"]!!)

  TODO: remove sorry from the lemma once sub-block specs carry enough
  information to reconstruct diff/expr_9/expr_6 in the Leave state.
  The spec shape itself is correct and sufficient for the balance
  invariant in fun_transferFundsToNTV_inner_balance_diff.
-/
def A_if_5678193105413593853 (s₀ s₉ : State) : Prop :=
  isLeave s₉ →
    s₉["var"]!! = 1 ∧
    s₉["diff"]!! = s₀["var_amount"]!! ∧
    s₉["diff"]!! = s₉["expr_9"]!! - s₉["expr_6"]!! ∧
    ¬(s₉["expr_9"]!! < s₉["expr_6"]!!)

lemma if_5678193105413593853_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5678193105413593853_concrete_of_code s₀ s₉ →
  Spec A_if_5678193105413593853 s₀ s₉ := by
  unfold if_5678193105413593853_concrete_of_code A_if_5678193105413593853
  sorry

end

end L1AssetRouter.Common
