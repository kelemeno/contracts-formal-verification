import Clear.ReasoningPrinciple
import specs.KeccakDistinct
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
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

/-! ### Growing the tree, step three

Allocate one word of scratch memory, put the new default node in it, and push that word
onto the LEVELS array at slot 2.  So this block writes slot 2's length and one keccak
image -- the third and last of the growth path's deliberate low-slot writes. -/

private lemma b5267_parts {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) {s₁ s₂ : State}
    (h₁ : Spec (A_allocate_memory "expr_mpos" 32) (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧) s₁)
    (h₂ : Spec (A_array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr 2
      ((s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧)["expr_mpos"]!!))
      (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧) s₂)
    (heq : s₉ = s₂) :
    ¬ ❓ s₁ ∧ isOk (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧) ∧ isOk s₁ := by
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    rw [heq] at hnf
    exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have hin : isOk (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧) := by simpa [isOk_insert] using hok
  exact ⟨h1nf, hin, allocate_memory_isOk h1nf (Spec_ok_unfold hin h1nf h₁)⟩

/-- **KECCAK WINDOW.**  Allocation keeps it, and the push keeps it. -/
lemma block_5267003775473151689_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm 2 < 18446744073709551616)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_block_5267003775473151689 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  obtain ⟨h1nf, hin, hs1⟩ := b5267_parts hok hnf h₁ h₂ heq
  rw [heq] at hnf ⊢
  have hine : (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧).evm = s₀.evm := by simp only [evm_insert]
  have hsl1 : ∀ q : Literal, Clear.EVMState.sload s₁.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q; rw [allocate_memory_sload hin h1nf (Spec_ok_unfold hin h1nf h₁), hine]
  obtain ⟨hR1, hC1⟩ := allocate_memory_config hin h1nf (by rw [hine]; exact hR)
    (by rw [hine]; exact hC) (Spec_ok_unfold hin h1nf h₁)
  have hmok : isOk (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧) := by
    simpa only [isOk_setEvm] using hs1
  have hme : (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧).evm
      = Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!) :=
    Clear.evm_setEvm_of_isOk hs1
  exact arrArrPush_config hmok hnf
    (by rw [hme, Clear.StorageFrame.sload_mstore, hsl1]; exact hfits)
    (by rw [hme]; exact Clear.StorageFrame.rangeInWindow_mstore hR1)
    (by rw [hme]; exact Clear.StorageFrame.cachedInWindow_mstore hC1)
    (Spec_ok_unfold hmok hnf h₂)

/-- **CLEAN FLAG, BACKWARDS.**  Allocation cannot dirty it; the push can.

No size hypothesis, deliberately: the caller above needs this flag in order to prove the
storage frames that would establish such a bound, so requiring one here would close a
circle.  `arrArrPush_clean_unconditional` is what makes that possible. -/
lemma block_5267003775473151689_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_5267003775473151689 s₀ s₉) : Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  obtain ⟨h1nf, hin, hs1⟩ := b5267_parts hok hnf h₁ h₂ heq
  rw [heq] at hnf hclean
  have hine : (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧).evm = s₀.evm := by simp only [evm_insert]
  have hsl1 : ∀ q : Literal, Clear.EVMState.sload s₁.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q; rw [allocate_memory_sload hin h1nf (Spec_ok_unfold hin h1nf h₁), hine]
  have hmok : isOk (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧) := by
    simpa only [isOk_setEvm] using hs1
  have hme : (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧).evm
      = Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!) :=
    Clear.evm_setEvm_of_isOk hs1
  have c1 := arrArrPush_clean_unconditional hmok hnf hclean (Spec_ok_unfold hmok hnf h₂)
  rw [hme, Clear.KeccakClean.clean_mstore] at c1
  rw [← hine]
  exact (allocate_memory_clean hin h1nf (Spec_ok_unfold hin h1nf h₁)).mp c1

set_option maxHeartbeats 800000 in
/-- **STORAGE FRAME: SLOT 2 AND NOTHING ELSE.**

The levels array's length lives at slot 2; the new element lands on a keccak image.  Every
other constant-numbered slot survives -- slot 1 included, which is what the leaf counter
needs from the growth path.

Third and last of the growth path's deliberate low-slot writes: slot 0 in `_6359`, slot 3
in `_3221`, slot 2 here. -/
lemma block_5267003775473151689_sload_of_ne {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm 2 < 18446744073709551616)
    (hc2 : c ≠ 2)
    (hclow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hlen : (Clear.EVMState.sload s₀.evm 2).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_5267003775473151689 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  obtain ⟨h1nf, hin, hs1⟩ := b5267_parts hok hnf h₁ h₂ heq
  rw [heq] at hnf hclean ⊢
  have hine : (s₀⟦"_6" ↦ 0⟧⟦"size" ↦ 32⟧).evm = s₀.evm := by simp only [evm_insert]
  have hsl1 : ∀ q : Literal, Clear.EVMState.sload s₁.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q; rw [allocate_memory_sload hin h1nf (Spec_ok_unfold hin h1nf h₁), hine]
  obtain ⟨hR1, hC1⟩ := allocate_memory_config hin h1nf (by rw [hine]; exact hR)
    (by rw [hine]; exact hC) (Spec_ok_unfold hin h1nf h₁)
  have hmok : isOk (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧) := by
    simpa only [isOk_setEvm] using hs1
  have hme : (s₁🇪⟦Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!)⟧).evm
      = Clear.EVMState.mstore s₁.evm (s₁["expr_mpos"]!!) (s₁["expr_1"]!!) :=
    Clear.evm_setEvm_of_isOk hs1
  -- the memory write changes no storage, so the push sees the caller's slot 2
  rw [arrArrPush_sload_of_low hmok hnf
      (by rw [hme, Clear.StorageFrame.sload_mstore, hsl1]; exact hfits) hc2 hclow
      (by rw [hme, Clear.StorageFrame.sload_mstore, hsl1]; exact hlen)
      (by rw [hme]; exact Clear.StorageFrame.rangeInWindow_mstore hR1)
      (by rw [hme]; exact Clear.StorageFrame.cachedInWindow_mstore hC1)
      hclean (Spec_ok_unfold hmok hnf h₂),
    hme, Clear.StorageFrame.sload_mstore, hsl1]

end

end L2InteropCommitmentTree.Common
