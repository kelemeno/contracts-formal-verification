import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_801497109727252421
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6033096439800527865
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5792510925045852942
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- **`finalize_allocation(memPtr, size)` — bump the free-memory pointer.**

Rounds `size` up to a word, adds it to `memPtr`, panics `0x41` if the result passes the
`2^64 - 1` ceiling or wraps below `memPtr`, and only then writes the new value to the
free pointer at memory offset 64.

The order is what matters: BOTH overflow tests happen before `mstore(64, …)`, so a
rejected allocation leaves the free pointer untouched. -/
def A_finalize_allocation (memPtr size : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec AtomicFlowManager.Common.A_block_801497109727252421
      (s₀☎️⟦["memPtr", "size"],[memPtr, size]⟧) s₁ ∧
    ∃ s₂, Spec AtomicFlowManager.Common.A_block_6033096439800527865 s₁ s₂ ∧
      ∃ s₃, Spec AtomicFlowManager.Common.A_if_5792510925045852942 s₂ s₃ ∧
        s₉ = 🧟(s₃🇪⟦Clear.EVMState.mstore s₃.evm 64 (s₃["newFreePtr"]!!)⟧)🏪⟦s₀⟧

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation memPtr size) s₀ s₉ := by
  unfold finalize_allocation_concrete_of_code A_finalize_allocation
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma finalize_allocation_isOk {memPtr size : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_finalize_allocation memPtr size s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump', isOutOfFuel_setEvm'] using hoo

lemma finalize_allocation_not_break {memPtr size : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_finalize_allocation memPtr size s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (finalize_allocation_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager
