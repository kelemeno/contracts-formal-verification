import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7714157185465443049
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4071781004081420828

import generated.AtomicFlowManager.AtomicFlowManager.update_storage_value_offset_enum_LegState_to_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

/-- **Transition a leg to `LegState` 2.**

Two blocks: read the slot and clear its low byte, then OR in the literal `2` and
`sstore` it back.  Two things follow from the shape, without any reasoning about
the caller:

- the value written is a CONSTANT.  The function takes only a slot, so it cannot
  write any state other than 2 — there is no path here that writes 1, 3, or a
  caller-chosen value;
- the rest of the packed slot is preserved, because the clear is
  `and(word, not(255))` rather than a wholesale zero.

Combined with the loop above it (which calls this only when the leg reads as state
1) that is the deployed 1 → 2 transition. -/
def A_update_storage_value_offset_enum_LegState_to_enum_LegState (slot : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec AtomicFlowManager.Common.A_block_7714157185465443049 (s₀☎️⟦["slot"],[slot]⟧) s₁ ∧
    ∃ s₂, Spec AtomicFlowManager.Common.A_block_7237915813042648898 s₁ s₂ ∧
      s₉ = 🧟s₂🏪⟦s₀⟧

lemma update_storage_value_offset_enum_LegState_to_enum_LegState_abs_of_concrete {s₀ s₉ : State} {slot} :
  Spec (update_storage_value_offset_enum_LegState_to_enum_LegState_concrete_of_code.1 slot) s₀ s₉ →
  Spec (A_update_storage_value_offset_enum_LegState_to_enum_LegState slot) s₀ s₉ := by
  unfold update_storage_value_offset_enum_LegState_to_enum_LegState_concrete_of_code A_update_storage_value_offset_enum_LegState_to_enum_LegState
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma update_storage_value_offset_enum_LegState_to_enum_LegState_isOk {slot : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_offset_enum_LegState_to_enum_LegState slot s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simp only [isOutOfFuel_setStore', isOutOfFuel_reviveJump']
  exact hoo

lemma update_storage_value_offset_enum_LegState_to_enum_LegState_not_break {slot : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_offset_enum_LegState_to_enum_LegState slot s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (update_storage_value_offset_enum_LegState_to_enum_LegState_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager
