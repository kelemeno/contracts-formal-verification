import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4720374723594237178_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The state after `let value_1 := 0; value_1 := calldataload(_3)`.  The inner
insert of `0` is the declaration; it is irrelevant to the `_3` lookup but the
generator emits it, so the spec keeps it. -/
def loadPrevBytes32 (s₁ : State) : State :=
  s₁⟦"value_1" ↦ Clear.EVMState.calldataload s₁.evm (s₁⟦"value_1"↦0⟧["_3"]!!)⟧

/-- **The compiled ascending-order check** (bytes32 arrays).

```
    let split_expr_0 := checked_sub_uint256(var_i)                       -- i - 1
    let _3 := calldata_array_index_access_bytes32_dyn_calldata(.., split_expr_0)
    value_1 := calldataload(_3)                                          -- arr[i-1]
    let split_expr_1 := gt(value, value_1)                               -- arr[i-1] < value
```

This is the deployed counterpart of `AttackVectors/FlowCanonical.lean`, which
proves what this NEIGHBOUR-ONLY comparison buys globally: run over every `i`, it
gives pairwise distinctness and uniqueness of the ordering — and that the cheaper
guard "adjacent entries differ" would NOT lift the same way.

The spec pins the whole chain: the decrement (with its underflow guard, so `i = 0`
reverts rather than wrapping to the array's end), the bounds-checked index access,
the load, and the comparison flag. -/
def A_block_4720374723594237178 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_checked_sub_uint256 "split_expr_0" (s₀["var_i"]!!)) s₀ s ∧
    ∃ s₁, Spec (A_calldata_array_index_access_bytes32_dyn_calldata "_3"
        (s["expr_661_offset"]!!) (s["expr_661_length"]!!) (s["split_expr_0"]!!)) s s₁ ∧
      s₉ = (loadPrevBytes32 s₁)⟦"split_expr_1" ↦
        if (loadPrevBytes32 s₁)["value_1"]!! < (loadPrevBytes32 s₁)["value"]!! then 1 else 0⟧

lemma block_4720374723594237178_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4720374723594237178_concrete_of_code s₀ s₉ →
  Spec A_block_4720374723594237178 s₀ s₉ := by
  unfold block_4720374723594237178_concrete_of_code A_block_4720374723594237178 loadPrevBytes32
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, s₁, hs₁, heq⟩ := hc
  exact ⟨s, hs, s₁, hs₁, heq.symm⟩

/-- **What the flag means**, stated entirely in terms of the block's OUTPUT state:
`split_expr_1` is nonzero exactly when the previous element is strictly below the
current one.  This is the per-step obligation the enclosing loop accumulates, and
the reading `FlowCanonical`'s abstract `ascending` assumes. -/
lemma block_4720374723594237178_flag_ne_zero_iff {s₀ s₉ : State} (hok : isOk s₉)
    (h : A_block_4720374723594237178 s₀ s₉) :
    s₉["split_expr_1"]!! ≠ 0 ↔ s₉["value_1"]!! < s₉["value"]!! := by
  obtain ⟨s, _, s₁, _, heq⟩ := h
  subst heq
  have hsv : isOk (loadPrevBytes32 s₁) := by rwa [isOk_insert] at hok
  rw [lookup_insert' hsv, lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  by_cases hlt : (loadPrevBytes32 s₁)["value_1"]!! < (loadPrevBytes32 s₁)["value"]!!
  · simp [hlt]
  · simp [hlt]

end

end AtomicFlowManager.Common
