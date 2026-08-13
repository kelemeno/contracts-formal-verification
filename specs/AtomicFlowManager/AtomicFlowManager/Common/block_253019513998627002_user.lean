import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_253019513998627002_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The state after `let value_1 := 0; value_1 := calldataload(_3)`.  The inner
insert of `0` is the declaration; it is irrelevant to the `_3` lookup but the
generator emits it, so the spec keeps it. -/
def loadPrevUint256 (s₁ : State) : State :=
  s₁⟦"value_1" ↦ Clear.EVMState.calldataload s₁.evm (s₁⟦"value_1"↦0⟧["_3"]!!)⟧

/-- **The compiled ascending-order check** (uint256 arrays).

```
    let split_expr_0 := checked_sub_uint256(var_i)                       -- i - 1
    let _3 := calldata_array_index_access_uint256_dyn_calldata(.., split_expr_0)
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
def A_block_253019513998627002 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_checked_sub_uint256 "split_expr_0" (s₀["var_i"]!!)) s₀ s ∧
    ∃ s₁, Spec (A_calldata_array_index_access_uint256_dyn_calldata "_3"
        (s["expr_594_offset"]!!) (s["expr_594_length"]!!) (s["split_expr_0"]!!)) s s₁ ∧
      s₉ = (loadPrevUint256 s₁)⟦"split_expr_1" ↦
        if (loadPrevUint256 s₁)["value_1"]!! < (loadPrevUint256 s₁)["value"]!! then 1 else 0⟧

lemma block_253019513998627002_abs_of_concrete {s₀ s₉ : State} :
  Spec block_253019513998627002_concrete_of_code s₀ s₉ →
  Spec A_block_253019513998627002 s₀ s₉ := by
  unfold block_253019513998627002_concrete_of_code A_block_253019513998627002 loadPrevUint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, s₁, hs₁, heq⟩ := hc
  exact ⟨s, hs, s₁, hs₁, heq.symm⟩

/-- **What the flag means**, stated entirely in terms of the block's OUTPUT state:
`split_expr_1` is nonzero exactly when the previous element is strictly below the
current one.  This is the per-step obligation the enclosing loop accumulates, and
the reading `FlowCanonical`'s abstract `ascending` assumes. -/
lemma block_253019513998627002_flag_ne_zero_iff {s₀ s₉ : State} (hok : isOk s₉)
    (h : A_block_253019513998627002 s₀ s₉) :
    s₉["split_expr_1"]!! ≠ 0 ↔ s₉["value_1"]!! < s₉["value"]!! := by
  obtain ⟨s, _, s₁, _, heq⟩ := h
  subst heq
  have hsv : isOk (loadPrevUint256 s₁) := by rwa [isOk_insert] at hok
  rw [lookup_insert' hsv, lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  by_cases hlt : (loadPrevUint256 s₁)["value_1"]!! < (loadPrevUint256 s₁)["value"]!!
  · simp [hlt]
  · simp [hlt]

/-- **Output is `Ok`.**  Same walk as block_932755155890173629, one call shorter,
ending in inserts rather than a call. -/
lemma block_253019513998627002_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_253019513998627002 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  subst heq
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    apply hnf
    simpa [loadPrevUint256, isOutOfFuel_insert'] using hoo
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_sub_uint256_isOk hok h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    calldata_array_index_access_uint256_dyn_calldata_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
  simpa [loadPrevUint256, isOk_insert] using hs2

lemma block_253019513998627002_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_253019513998627002 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_253019513998627002_isOk hok hnf h)

end

end AtomicFlowManager.Common
