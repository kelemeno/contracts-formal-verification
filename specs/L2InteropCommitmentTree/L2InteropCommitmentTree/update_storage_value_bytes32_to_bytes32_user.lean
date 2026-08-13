import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7182708311549001418
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

/-- **Write a `bytes32` into a storage slot at a byte offset.**

Two blocks: build the mask for the field at `offset`, then clear that field and OR
the shifted value in before `sstore`.  Callers in the array-push path pass
`offset = 0`, where the mask is `0` and this writes `value` as the whole word.

Only ONE slot is written, and which slot is the caller's argument -- there is no
path here that touches a second slot. -/
def A_update_storage_value_bytes32_to_bytes32 (slot offset value : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_block_7182708311549001418
      (s₀☎️⟦["slot", "offset", "value"],[slot, offset, value]⟧) s₁ ∧
    ∃ s₂, Spec L2InteropCommitmentTree.Common.A_block_8692170500034331446 s₁ s₂ ∧
      s₉ = 🧟s₂🏪⟦s₀⟧

lemma update_storage_value_bytes32_to_bytes32_abs_of_concrete {s₀ s₉ : State} {slot offset value} :
  Spec (update_storage_value_bytes32_to_bytes32_concrete_of_code.1 slot offset value) s₀ s₉ →
  Spec (A_update_storage_value_bytes32_to_bytes32 slot offset value) s₀ s₉ := by
  unfold update_storage_value_bytes32_to_bytes32_concrete_of_code A_update_storage_value_bytes32_to_bytes32
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma update_storage_value_bytes32_to_bytes32_isOk {slot offset value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma update_storage_value_bytes32_to_bytes32_not_break {slot offset value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (update_storage_value_bytes32_to_bytes32_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
