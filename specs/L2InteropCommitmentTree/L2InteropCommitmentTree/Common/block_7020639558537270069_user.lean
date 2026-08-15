import Clear.ReasoningPrinciple
import specs.KeccakDistinct
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7020639558537270069_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Copy level `i`'s node from one array into the other.**

```
    _7, _8  := storage_array_index_access(2, var_i)     -- destination array, slot 2
    _9, _10 := storage_array_index_access(3, var_i)     -- source array, slot 3
    split_expr_7 := sload(_9)
    split_expr_8 := extract_from_storage_value_dynamict_bytes32(split_expr_7, _10)
    array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr(_7, split_expr_8)
```

Both array slots are LITERALS (2 and 3), so the loop cannot be steered onto another
array: the only caller-influenced quantity is the level index `var_i`, and both
accesses are bounds-checked against their own array's length.  The value pushed is
the one just read from the source array at the same index. -/
def A_block_7020639558537270069 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_7" "_8" 2 (s₀["var_i"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_9" "_10" 3 (s₁["var_i"]!!)) s₁ s₂ ∧
      (let ld := s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧
       ∃ s₃, Spec (A_extract_from_storage_value_dynamict_bytes32 "split_expr_8"
           (ld["split_expr_7"]!!) (ld["_10"]!!)) ld s₃ ∧
         ∃ s₄, Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
             (s₃["_7"]!!) (s₃["split_expr_8"]!!)) s₃ s₄ ∧
           s₉ = s₄)

lemma block_7020639558537270069_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7020639558537270069_concrete_of_code s₀ s₉ →
  Spec A_block_7020639558537270069 s₀ s₉ := by
  unfold block_7020639558537270069_concrete_of_code A_block_7020639558537270069
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, rest⟩ := hc
  exact ⟨s₁, h₁, by
    obtain ⟨s₂, h₂, rest2⟩ := rest
    exact ⟨s₂, h₂, by
      first
        | exact rest2.symm
        | (obtain ⟨s₃, h₃, s₄, h₄, heq⟩ := rest2; exact ⟨s₃, h₃, s₄, h₄, heq.symm⟩)⟩⟩

/-- Output is `Ok`: four function returns in sequence, `hnf` walked backwards. -/
lemma block_7020639558537270069_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_7020639558537270069 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    exact h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
      (by simpa [isOutOfFuel_insert'] using hoo))
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hld : isOk (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) := by
    simpa [isOk_insert] using hs2
  have hs3 : isOk s₃ :=
    extract_from_storage_value_dynamict_bytes32_isOk h3nf (Spec_ok_unfold hld h3nf h₃)
  exact array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk hnf
    (Spec_ok_unfold hs3 hnf h₄)

lemma block_7020639558537270069_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_7020639558537270069 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_7020639558537270069_isOk hok hnf h)

/-! ### Copying a level's node into the extended tree

Read level `i`'s array (slot 2) and the defaults array (slot 3) at index `i`, take the
default's value, and push it onto level `i`'s array.

The push's target is `_7` -- the address the FIRST accessor returned, so a keccak image
rather than a literal slot.  That is what makes this block preserve every constant-numbered
slot outright, unlike its siblings on the growth path: there is no literal slot for it to
write.  The accessor's own `_slot_not_low_of_clean` is what supplies `c ≠ _7`. -/

private lemma b7020_chain {s₉ : State} (hnf : ¬ ❓ s₉) {s₁ s₂ s₃ s₄ : State}
    (h₂ : Spec (A_storage_array_index_access_bytes32_dyn_ptr "_9" "_10" 3 (s₁["var_i"]!!))
      s₁ s₂)
    (h₃ : Spec (A_extract_from_storage_value_dynamict_bytes32 "split_expr_8"
      ((s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧)["split_expr_7"]!!)
      ((s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧)["_10"]!!))
      (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) s₃)
    (h₄ : Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
      (s₃["_7"]!!) (s₃["split_expr_8"]!!)) s₃ s₄)
    (heq : s₉ = s₄) : ¬ ❓ s₄ ∧ ¬ ❓ s₃ ∧ ¬ ❓ s₂ ∧ ¬ ❓ s₁ := by
  have h4nf : ¬ ❓ s₄ := by rw [heq] at hnf; exact hnf
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
    (by simpa only [isOutOfFuel_insert'] using hoo))
  exact ⟨h4nf, h3nf, h2nf,
    fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)⟩

/-- **KECCAK WINDOW.**  Two accessor hashes, a pure extract, and the push. -/
lemma block_7020639558537270069_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hfits : ∀ q : Literal, Clear.EVMState.sload s₀.evm q < 18446744073709551616)
    (h : A_block_7020639558537270069 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  obtain ⟨h4nf, h3nf, h2nf, h1nf⟩ := b7020_chain hnf h₂ h₃ h₄ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := storage_array_index_access_bytes32_dyn_ptr_isOk h1nf a₁
  obtain ⟨hR1, hC1⟩ := storage_array_index_access_bytes32_dyn_ptr_config hok h1nf hR hC a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := storage_array_index_access_bytes32_dyn_ptr_isOk h2nf a₂
  obtain ⟨hR2, hC2⟩ := storage_array_index_access_bytes32_dyn_ptr_config hs1 h2nf hR1 hC1 a₂
  have hldok : isOk (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) :=
    isOk_insert.mpr hs2
  have a₃ := Spec_ok_unfold hldok h3nf h₃
  have hs3 : isOk s₃ := extract_from_storage_value_dynamict_bytes32_isOk h3nf a₃
  have e3 : s₃.evm = s₂.evm := by
    rw [extract_from_storage_value_dynamict_bytes32_evm hldok a₃, evm_insert]
  -- storage is untouched all the way to the push, so the caller's bound still applies
  have esl : ∀ q : Literal, Clear.EVMState.sload s₃.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q
    rw [e3, storage_array_index_access_bytes32_dyn_ptr_sload hs1 h2nf a₂,
      storage_array_index_access_bytes32_dyn_ptr_sload hok h1nf a₁]
  obtain ⟨hR4, hC4⟩ := array_push_config hs3 h4nf
    (by rw [esl]; exact hfits _) (by rw [e3]; exact hR2) (by rw [e3]; exact hC2)
    (Spec_ok_unfold hs3 h4nf h₄)
  subst heq
  exact ⟨hR4, hC4⟩

/-- **CLEAN FLAG, BACKWARDS.**  Three hashes: an accessor each for the level and defaults
arrays, and the push's own address computation. -/
lemma block_7020639558537270069_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : ∀ q : Literal, Clear.EVMState.sload s₀.evm q < 18446744073709551616)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_7020639558537270069 s₀ s₉) : Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  obtain ⟨h4nf, h3nf, h2nf, h1nf⟩ := b7020_chain hnf h₂ h₃ h₄ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := storage_array_index_access_bytes32_dyn_ptr_isOk h1nf a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := storage_array_index_access_bytes32_dyn_ptr_isOk h2nf a₂
  have hldok : isOk (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) :=
    isOk_insert.mpr hs2
  have a₃ := Spec_ok_unfold hldok h3nf h₃
  have hs3 : isOk s₃ := extract_from_storage_value_dynamict_bytes32_isOk h3nf a₃
  have e3 : s₃.evm = s₂.evm := by
    rw [extract_from_storage_value_dynamict_bytes32_evm hldok a₃, evm_insert]
  have esl : ∀ q : Literal, Clear.EVMState.sload s₃.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q
    rw [e3, storage_array_index_access_bytes32_dyn_ptr_sload hs1 h2nf a₂,
      storage_array_index_access_bytes32_dyn_ptr_sload hok h1nf a₁]
  rw [heq] at hclean
  have c3 : Clear.KeccakClean.Clean s₃.evm :=
    array_push_clean hs3 h4nf (by rw [esl]; exact hfits _) hclean (Spec_ok_unfold hs3 h4nf h₄)
  rw [e3] at c3
  exact storage_array_index_access_bytes32_dyn_ptr_clean hok h1nf
    (storage_array_index_access_bytes32_dyn_ptr_clean hs1 h2nf c3 a₂) a₁

/-- **THIS BLOCK WRITES NO CONSTANT-NUMBERED SLOT AT ALL.**

Unlike its siblings on the growth path, which raise the height at slot 0 or extend an array
at slot 2 or 3, the copy block's push targets `_7` -- the address the FIRST accessor
returned.  That is a keccak image, so there is no literal slot for it to write, and the
separation comes from the accessor's own `_slot_not_low_of_clean` rather than from a
case split on which slot was meant.

`hj2` and `hj3` are the index bounds the two accessors owe; both are about the loop's level
counter, which any real tree keeps far below `2 ^ 32`. -/
lemma block_7020639558537270069_sload_of_low {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hfits : ∀ q : Literal, Clear.EVMState.sload s₀.evm q < 18446744073709551616)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (hclow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hj : (s₀["var_i"]!!).val < Clear.KeccakInjective.lowSlotBound)
    (hlen : ∀ q : Literal,
      (Clear.EVMState.sload s₀.evm q).val < Clear.KeccakInjective.lowSlotBound)
    (h : A_block_7020639558537270069 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  obtain ⟨h4nf, h3nf, h2nf, h1nf⟩ := b7020_chain hnf h₂ h₃ h₄ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := storage_array_index_access_bytes32_dyn_ptr_isOk h1nf a₁
  obtain ⟨hR1, hC1⟩ := storage_array_index_access_bytes32_dyn_ptr_config hok h1nf hR hC a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := storage_array_index_access_bytes32_dyn_ptr_isOk h2nf a₂
  obtain ⟨hR2, hC2⟩ := storage_array_index_access_bytes32_dyn_ptr_config hs1 h2nf hR1 hC1 a₂
  have hldok : isOk (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) :=
    isOk_insert.mpr hs2
  have a₃ := Spec_ok_unfold hldok h3nf h₃
  have hs3 : isOk s₃ := extract_from_storage_value_dynamict_bytes32_isOk h3nf a₃
  have e3 : s₃.evm = s₂.evm := by
    rw [extract_from_storage_value_dynamict_bytes32_evm hldok a₃, evm_insert]
  have esl : ∀ q : Literal, Clear.EVMState.sload s₃.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q
    rw [e3, storage_array_index_access_bytes32_dyn_ptr_sload hs1 h2nf a₂,
      storage_array_index_access_bytes32_dyn_ptr_sload hok h1nf a₁]
  rw [heq] at hclean ⊢
  -- the pushed-to array is `_7`, a keccak image: the first accessor says it is not `c`
  have c3 : Clear.KeccakClean.Clean s₃.evm :=
    array_push_clean hs3 h4nf (by rw [esl]; exact hfits _) hclean (Spec_ok_unfold hs3 h4nf h₄)
  have c1 : Clear.KeccakClean.Clean s₁.evm := by
    rw [e3] at c3
    exact storage_array_index_access_bytes32_dyn_ptr_clean hs1 h2nf c3 a₂
  have hne : s₁["_7"]!! ≠ c :=
    storage_array_index_access_bytes32_dyn_ptr_slot_not_low_of_clean hok h1nf hR hC c1
      hj hclow a₁
  have h7 : s₃["_7"]!! = s₁["_7"]!! := by
    rw [extract_from_storage_value_dynamict_bytes32_frame hldok h3nf (by decide) a₃,
      lookup_insert_of_ne (by decide),
      storage_array_index_access_bytes32_dyn_ptr_frame hs1 h2nf (by decide) (by decide) a₂]
  rw [array_push_sload_frame_of_low_slot_of_clean hs3 h4nf (by rw [esl]; exact hfits _)
      (by rw [h7]; exact Ne.symm hne) hclow (by rw [esl]; exact hlen _) (by rw [e3]; exact hR2)
      (by rw [e3]; exact hC2) hclean (Spec_ok_unfold hs3 h4nf h₄), esl]

/-- **CLEAN FLAG, BACKWARDS, WITH NO SIDE CONDITION.**  The `hfits`-free companion, built
on `array_push_clean_unconditional`.  This is the form the loop induction needs: inside the
loop nobody knows the level array is small, and the flag is supposed to cost nothing. -/
lemma block_7020639558537270069_clean_unconditional {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_7020639558537270069 s₀ s₉) : Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  obtain ⟨h4nf, h3nf, h2nf, h1nf⟩ := b7020_chain hnf h₂ h₃ h₄ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := storage_array_index_access_bytes32_dyn_ptr_isOk h1nf a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := storage_array_index_access_bytes32_dyn_ptr_isOk h2nf a₂
  have hldok : isOk (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) :=
    isOk_insert.mpr hs2
  have a₃ := Spec_ok_unfold hldok h3nf h₃
  have hs3 : isOk s₃ := extract_from_storage_value_dynamict_bytes32_isOk h3nf a₃
  have e3 : s₃.evm = s₂.evm := by
    rw [extract_from_storage_value_dynamict_bytes32_evm hldok a₃, evm_insert]
  rw [heq] at hclean
  have c3 : Clear.KeccakClean.Clean s₃.evm :=
    array_push_clean_unconditional hs3 h4nf hclean (Spec_ok_unfold hs3 h4nf h₄)
  rw [e3] at c3
  exact storage_array_index_access_bytes32_dyn_ptr_clean hok h1nf
    (storage_array_index_access_bytes32_dyn_ptr_clean hs1 h2nf c3 a₂) a₁

end

end L2InteropCommitmentTree.Common
