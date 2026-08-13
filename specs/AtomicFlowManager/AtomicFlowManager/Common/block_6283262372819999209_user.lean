import Clear.ReasoningPrinciple

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

end

end AtomicFlowManager.Common
