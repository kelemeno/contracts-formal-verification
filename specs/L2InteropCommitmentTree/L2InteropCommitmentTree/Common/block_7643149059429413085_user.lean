import Clear.ReasoningPrinciple
import specs.StateOk
import specs.KeccakLowSlot
import specs.StorageFrame

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7643149059429413085_gen


namespace L2InteropCommitmentTree.Common

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The node write**, generic-tree variant:
`update_storage_value_bytes32_to_bytes32(_18, _19, var_currentHash)`.

Same as `block_2896862189596047701` but in the copy of the fold where the tree's
storage location is a PARAMETER rather than the literal slot 2 -- so the locals are
numbered one higher.  The value written is still the running hash and nothing else. -/
def A_block_7643149059429413085 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_update_storage_value_bytes32_to_bytes32
      (s₀["_18"]!!) (s₀["_19"]!!) (s₀["var_currentHash"]!!)) s₀ s ∧ s₉ = s

lemma block_7643149059429413085_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7643149059429413085_concrete_of_code s₀ s₉ →
  Spec A_block_7643149059429413085 s₀ s₉ := by
  unfold block_7643149059429413085_concrete_of_code A_block_7643149059429413085
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, heq⟩ := hc
  exact ⟨s, hs, heq.symm⟩

lemma block_7643149059429413085_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_7643149059429413085 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact update_storage_value_bytes32_to_bytes32_isOk hnf (Spec_ok_unfold hok hnf hs)

lemma block_7643149059429413085_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_7643149059429413085 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_7643149059429413085_isOk hok hnf h)


/-- **TOTAL FRAME.**  The block is one call to the storage writer, so it too leaves every
local alone: the new node goes to storage, not to a variable. -/
lemma block_7643149059429413085_frame {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_block_7643149059429413085 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact update_storage_value_bytes32_to_bytes32_frame hok hnf (Spec_ok_unfold hok hnf hs)


/-- **STORAGE FRAME.**  The loop's write block stores the new node at `_17` and nowhere
else, so every other slot survives one iteration's write. -/
lemma block_7643149059429413085_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (hq : q ≠ s₀["_18"]!!) (h : A_block_7643149059429413085 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact update_storage_value_bytes32_to_bytes32_sload_frame hok hnf hq
    (Spec_ok_unfold hok hnf hs)


/-- **CONFIG FRAME.**  One storage write; the window is untouched. -/
lemma block_7643149059429413085_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_block_7643149059429413085 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact update_storage_value_bytes32_to_bytes32_config hok hnf hR hC
    (Spec_ok_unfold hok hnf hs)

end

end L2InteropCommitmentTree.Common
