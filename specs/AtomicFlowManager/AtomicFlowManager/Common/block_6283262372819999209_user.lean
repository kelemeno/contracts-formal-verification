import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6283262372819999209_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- State after `let value := 0; value := calldataload(_2)`. -/
def loadValBytes32 (s : State) : State :=
  s⟦"value" ↦ Clear.EVMState.calldataload s.evm ((s⟦"value" ↦ 0⟧)["_2"]!!)⟧

/-- **The loop body's element read** (bytes32).

```
    expr_657_offset, expr_657_length := access_calldata_tail_array(var_flow_offset, _1)
    _2    := calldata_array_index_access(expr_657_offset, expr_657_length, var_i)
    value := calldataload(_2)                     -- arr[i]
    expr_661_offset, expr_661_length := access_calldata_tail_array(var_flow_offset, _1)
```

Note the tail is decoded TWICE — solc recomputes the accessor for the second use
rather than reusing the first result — so the full bounds discipline of
`access_calldata_tail_array_*` runs again before `block_4720374723594237178`
indexes with `i - 1`.  That redundancy is why the neighbour comparison's two reads
are each independently bounds-checked, rather than one inheriting the other's
check.

With this closed, `value` is the current element and `expr_661_*` the re-derived
tail the previous-element read uses. -/
def A_block_6283262372819999209 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_access_calldata_tail_array_bytes32_dyn_calldata
      "expr_657_offset" "expr_657_length" (s₀["var_flow_offset"]!!) (s₀["_1"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_calldata_array_index_access_bytes32_dyn_calldata "_2"
        (s₁["expr_657_offset"]!!) (s₁["expr_657_length"]!!) (s₁["var_i"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_access_calldata_tail_array_bytes32_dyn_calldata
          "expr_661_offset" "expr_661_length"
          ((loadValBytes32 s₂)["var_flow_offset"]!!) ((loadValBytes32 s₂)["_1"]!!))
          (loadValBytes32 s₂) s₃ ∧
        s₉ = s₃

lemma block_6283262372819999209_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6283262372819999209_concrete_of_code s₀ s₉ →
  Spec A_block_6283262372819999209 s₀ s₉ := by
  unfold block_6283262372819999209_concrete_of_code A_block_6283262372819999209 loadValBytes32
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- **Output is `Ok`.**  Walks the three-call chain.  No case split on the
intermediates is needed: an out-of-fuel intermediate would force `❓ s₉` through the
remaining `Spec`s, which `hnf` excludes, and a `Checkpoint` intermediate cannot
arise because each producer is a function call whose result is `🧟`-shaped. -/
lemma block_6283262372819999209_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_6283262372819999209 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  subst heq
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
      (by simpa [loadValBytes32, isOutOfFuel_insert'] using hoo))
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    access_calldata_tail_array_bytes32_dyn_calldata_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    calldata_array_index_access_bytes32_dyn_calldata_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hload : isOk (loadValBytes32 s₂) := by
    simpa [loadValBytes32, isOk_insert] using hs2
  exact access_calldata_tail_array_bytes32_dyn_calldata_isOk hnf (Spec_ok_unfold hload hnf h₃)

lemma block_6283262372819999209_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_6283262372819999209 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_6283262372819999209_isOk hok hnf h)

end

end AtomicFlowManager.Common
