import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7643149059429413085_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

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

end

end L2InteropCommitmentTree.Common
