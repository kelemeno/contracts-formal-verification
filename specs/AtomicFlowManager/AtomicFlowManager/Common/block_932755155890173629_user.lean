import Clear.ReasoningPrinciple

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

end

end AtomicFlowManager.Common
