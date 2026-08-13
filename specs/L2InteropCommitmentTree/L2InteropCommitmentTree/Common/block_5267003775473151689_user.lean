import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5267003775473151689_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Grow the tree by one level, part 3: give the new level its node.**

```
    expr_mpos := allocate_memory(32)
    mstore(expr_mpos, expr_1)
    array_push_from_array_…(2, expr_mpos)
```

`expr_1` is the new level's empty-subtree default, computed in part 2 as `hash(d, d)`.
Here it is written into a fresh 32-byte memory buffer and pushed into the LEVELS array
at slot 2 as a one-element array.

So growing the tree adds the same value in two places: to the DEFAULTS array (part 2),
where it stays as `defaults[newLevel]`, and as the new top level's single node.  That is
correct precisely because a tree that has just grown is empty above the old root -- the
new level's only node IS an empty subtree of that height. -/
def A_block_5267003775473151689 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_allocate_memory "expr_mpos" 32) (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧) s₁ ∧
    (let m := s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧
     ∃ s₂, Spec (A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr 2 (m["expr_mpos"]!!)) m s₂ ∧
       s₉ = s₂)

lemma block_5267003775473151689_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5267003775473151689_concrete_of_code s₀ s₉ →
  Spec A_block_5267003775473151689 s₀ s₉ := by
  unfold block_5267003775473151689_concrete_of_code A_block_5267003775473151689
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, heq.symm⟩

lemma block_5267003775473151689_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_5267003775473151689 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  rw [heq] at hnf ⊢
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have hin : isOk (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧) := by simpa [isOk_insert] using hok
  have hs1 : isOk s₁ := allocate_memory_isOk h1nf (Spec_ok_unfold hin h1nf h₁)
  have hmok : isOk (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧) := by
    simpa only [isOk_setEvm] using hs1
  exact array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr_isOk hnf
    (Spec_ok_unfold hmok hnf h₂)

lemma block_5267003775473151689_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_5267003775473151689 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_5267003775473151689_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
