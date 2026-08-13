import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8934115175442537836_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- **Read a leg's state and test it against 1.**

```
    split_expr_8 := mapping_index_access(split_expr_7, value_5)   -- legState[flow][leg]
    _5           := read_from_storage_split_offset_enum_LegState(split_expr_8)
    validator_assert_enum_LegState(_5)                            -- panics unless < 4
    split_expr_9 := eq(_5, 1)
```

The assertion sits BETWEEN the read and the test, so by the time the flag is
computed the byte is known to be a valid `LegState`.  The flag is what the skip
guard `if_2726844535930192361` then branches on. -/
def A_block_8934115175442537836 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
      "split_expr_8" (s₀["split_expr_7"]!!) (s₀["value_5"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_read_from_storage_split_offset_enum_LegState "_5" (s₁["split_expr_8"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_validator_assert_enum_LegState (s₂["_5"]!!)) s₂ s₃ ∧
        s₉ = s₃⟦"split_expr_9" ↦ if s₃["_5"]!! = 1 then 1 else 0⟧

lemma block_8934115175442537836_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8934115175442537836_concrete_of_code s₀ s₉ →
  Spec A_block_8934115175442537836 s₀ s₉ := by
  unfold block_8934115175442537836_concrete_of_code A_block_8934115175442537836
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- **What the flag means**, on the block's output state: the leg is in state 1
exactly when `split_expr_9` is nonzero.  This is the condition the loop uses to
decide whether to transition the leg, so it is the per-leg precondition of the
1 → 2 write. -/
lemma block_8934115175442537836_flag_ne_zero_iff {s₀ s₉ : State} (hok : isOk s₉)
    (h : A_block_8934115175442537836 s₀ s₉) : s₉["split_expr_9"]!! ≠ 0 ↔ s₉["_5"]!! = 1 := by
  obtain ⟨s₁, _, s₂, _, s₃, _, heq⟩ := h
  subst heq
  have h3 : isOk s₃ := by rwa [isOk_insert] at hok
  rw [lookup_insert' h3, lookup_insert_of_ne (by decide)]
  by_cases hv : s₃["_5"]!! = 1
  · simp [hv]
  · simp [hv]

/-- Output is `Ok`.  Each intermediate is a function return, so out-of-fuel is the
only failure mode; `hnf` walks backwards through the chain and refutes it. -/
lemma block_8934115175442537836_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_8934115175442537836 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  subst heq
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_isOk h1nf
      (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    read_from_storage_split_offset_enum_LegState_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ :=
    validator_assert_enum_LegState_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  simpa [isOk_insert] using hs3

lemma block_8934115175442537836_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_8934115175442537836 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_8934115175442537836_isOk hok hnf h)

end

end AtomicFlowManager.Common
