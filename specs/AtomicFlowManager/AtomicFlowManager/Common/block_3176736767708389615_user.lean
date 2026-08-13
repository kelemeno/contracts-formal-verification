import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3176736767708389615_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- State after `let value_5 := 0; value_5 := calldataload(_4)` — the leg id at index `i`. -/
def loadLegId (s : State) : State :=
  s⟦"value_5" ↦ Clear.EVMState.calldataload s.evm ((s⟦"value_5" ↦ 0⟧)["_4"]!!)⟧

/-- **Read leg `i` and derive its state slot.**

```
    expr_399_offset, expr_length := access_calldata_tail_array(var__flow_offset, _2)
    _4           := calldata_array_index_access(expr_399_offset, expr_length, var_i)
    value_5      := calldataload(_4)                    -- the leg id
    split_expr_7 := mapping_index_access_…_7848(value_3) -- legState[flow], outer slot
```

The leg id comes from CALLDATA through the bounds-checked accessor, and the outer
mapping slot is derived from `value_3` (the flow id) — so the pair `(flow, leg)`
that block_8934115175442537836 then indexes is exactly the caller's argument and
the calldata element, with no other provenance. -/
def A_block_3176736767708389615 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_access_calldata_tail_array_bytes32_dyn_calldata
      "expr_399_offset" "expr_length" (s₀["var__flow_offset"]!!) (s₀["_2"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_calldata_array_index_access_bytes32_dyn_calldata "_4"
        (s₁["expr_399_offset"]!!) (s₁["expr_length"]!!) (s₁["var_i"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848 "split_expr_7" ((loadLegId s₂)["value_3"]!!)) (loadLegId s₂) s₃ ∧
        s₉ = s₃

lemma block_3176736767708389615_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3176736767708389615_concrete_of_code s₀ s₉ →
  Spec A_block_3176736767708389615 s₀ s₉ := by
  unfold block_3176736767708389615_concrete_of_code A_block_3176736767708389615 loadLegId
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- Output is `Ok`: three function returns in a row, so out-of-fuel is the only
failure mode and `hnf` refutes it backwards along the chain. -/
lemma block_3176736767708389615_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3176736767708389615 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  subst heq
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
      (by simpa [loadLegId, isOutOfFuel_insert'] using hoo))
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    access_calldata_tail_array_bytes32_dyn_calldata_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    calldata_array_index_access_bytes32_dyn_calldata_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hload : isOk (loadLegId s₂) := by simpa [loadLegId, isOk_insert] using hs2
  exact mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848_isOk hnf (Spec_ok_unfold hload hnf h₃)

lemma block_3176736767708389615_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3176736767708389615 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_3176736767708389615_isOk hok hnf h)

end

end AtomicFlowManager.Common
