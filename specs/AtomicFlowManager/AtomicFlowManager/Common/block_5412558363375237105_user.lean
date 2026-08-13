import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5412558363375237105_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- **Is this leg revertable?**  Read its state, assert validity, test against 2.

```
    _5 := read_from_storage_split_offset_enum_LegState(split_expr_21)
    validator_assert_enum_LegState(_5)
    split_expr_22 := eq(_5, 2)
```

State 2 is the one the leg loop transitions TO (`or(cleared, 2)` in
update_storage_value_offset_enum_LegState), so this asks "has this leg been through the
transition?" -- and `if_880639588767859599` reverts with
`ManagerLegNotRevertable(flowId, legId, state)` when it has not. -/
def A_block_5412558363375237105 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_read_from_storage_split_offset_enum_LegState "_5"
      (s₀["split_expr_21"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_validator_assert_enum_LegState (s₁["_5"]!!)) s₁ s₂ ∧
      s₉ = s₂⟦"split_expr_22" ↦ if s₂["_5"]!! = 2 then 1 else 0⟧

lemma block_5412558363375237105_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5412558363375237105_concrete_of_code s₀ s₉ →
  Spec A_block_5412558363375237105 s₀ s₉ := by
  unfold block_5412558363375237105_concrete_of_code A_block_5412558363375237105
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, heq.symm⟩

/-- **What the flag means**, on the output state: the leg is in state 2 exactly when
`split_expr_22` is nonzero. -/
lemma block_5412558363375237105_flag_ne_zero_iff {s₀ s₉ : State} (hok : isOk s₉)
    (h : A_block_5412558363375237105 s₀ s₉) : s₉["split_expr_22"]!! ≠ 0 ↔ s₉["_5"]!! = 2 := by
  obtain ⟨s₁, _, s₂, _, heq⟩ := h
  subst heq
  have h2 : isOk s₂ := by rwa [isOk_insert] at hok
  rw [lookup_insert' h2, lookup_insert_of_ne (by decide)]
  by_cases hv : s₂["_5"]!! = 2
  · simp [hv]
  · simp [hv]

lemma block_5412558363375237105_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_5412558363375237105 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  rw [heq] at hnf ⊢
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    read_from_storage_split_offset_enum_LegState_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    validator_assert_enum_LegState_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
  simpa [isOk_insert] using hs2

lemma block_5412558363375237105_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_5412558363375237105 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_5412558363375237105_isOk hok hnf h)

end

end AtomicFlowManager.Common
