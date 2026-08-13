import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_932755155890173629_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- State after `let value := 0; value := calldataload(_2)`. -/
def loadValUint256 (s : State) : State :=
  s⟦"value" ↦ Clear.EVMState.calldataload s.evm ((s⟦"value" ↦ 0⟧)["_2"]!!)⟧

/-- **The loop body's element read** (uint256).

```
    expr_590_offset, expr_590_length := access_calldata_tail_array(var_flow_offset, _1)
    _2    := calldata_array_index_access(expr_590_offset, expr_590_length, var_i)
    value := calldataload(_2)                     -- arr[i]
    expr_594_offset, expr_594_length := access_calldata_tail_array(var_flow_offset, _1)
```

Note the tail is decoded TWICE — solc recomputes the accessor for the second use
rather than reusing the first result — so the full bounds discipline of
`access_calldata_tail_array_*` runs again before `block_4720374723594237178`
indexes with `i - 1`.  That redundancy is why the neighbour comparison's two reads
are each independently bounds-checked, rather than one inheriting the other's
check.

With this closed, `value` is the current element and `expr_594_*` the re-derived
tail the previous-element read uses. -/
def A_block_932755155890173629 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_access_calldata_tail_array_uint256_dyn_calldata
      "expr_590_offset" "expr_590_length" (s₀["var_flow_offset"]!!) (s₀["_1"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_calldata_array_index_access_uint256_dyn_calldata "_2"
        (s₁["expr_590_offset"]!!) (s₁["expr_590_length"]!!) (s₁["var_i"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_access_calldata_tail_array_uint256_dyn_calldata
          "expr_594_offset" "expr_594_length"
          ((loadValUint256 s₂)["var_flow_offset"]!!) ((loadValUint256 s₂)["_1"]!!))
          (loadValUint256 s₂) s₃ ∧
        s₉ = s₃

lemma block_932755155890173629_abs_of_concrete {s₀ s₉ : State} :
  Spec block_932755155890173629_concrete_of_code s₀ s₉ →
  Spec A_block_932755155890173629 s₀ s₉ := by
  unfold block_932755155890173629_concrete_of_code A_block_932755155890173629 loadValUint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- **Output is `Ok`.**  Walks the three-call chain.  No case split on the
intermediates is needed: an out-of-fuel intermediate would force `❓ s₉` through the
remaining `Spec`s, which `hnf` excludes, and a `Checkpoint` intermediate cannot
arise because each producer is a function call whose result is `🧟`-shaped. -/
lemma block_932755155890173629_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_932755155890173629 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  subst heq
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
      (by simpa [loadValUint256, isOutOfFuel_insert'] using hoo))
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    access_calldata_tail_array_uint256_dyn_calldata_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    calldata_array_index_access_uint256_dyn_calldata_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hload : isOk (loadValUint256 s₂) := by
    simpa [loadValUint256, isOk_insert] using hs2
  exact access_calldata_tail_array_uint256_dyn_calldata_isOk hnf (Spec_ok_unfold hload hnf h₃)

lemma block_932755155890173629_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_932755155890173629 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_932755155890173629_isOk hok hnf h)

end

end AtomicFlowManager.Common
