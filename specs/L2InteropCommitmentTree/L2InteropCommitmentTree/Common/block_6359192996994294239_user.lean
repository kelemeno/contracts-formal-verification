import Clear.ReasoningPrinciple
import specs.KeccakFuel
import specs.KeccakDistinct
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6359192996994294239_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Grow the tree by one level, part 1: bump the level count and read the top default.**

```
    expr := fun_uncheckedInc(_2)            -- levels + 1, UNCHECKED
    sstore(0, expr)                         -- store the new level count
    split_expr_2 := checked_sub_uint256(expr)   -- (levels + 1) - 1, CHECKED
    _3, _4 := storage_array_index_access(3, split_expr_2)  -- defaults[levels]
    split_expr_3 := sload(_3)
```

The level count is written BEFORE the new level's node exists, and the default read is
at the OLD top index (`(levels+1) - 1 = levels`), so this reads the default that was
previously the topmost -- the input to the new one computed in part 2. -/
def A_block_6359192996994294239 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_fun_uncheckedInc "expr" (s₀["_2"]!!)) s₀ s₁ ∧
    (let st := s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧
     ∃ s₂, Spec (A_checked_sub_uint256 "split_expr_2" (st["expr"]!!)) st s₂ ∧
       ∃ s₃, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_3" "_4" 3
           (s₂["split_expr_2"]!!)) s₂ s₃ ∧
         s₉ = s₃⟦"split_expr_3" ↦ Clear.EVMState.sload s₃.evm (s₃["_3"]!!)⟧)

lemma block_6359192996994294239_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6359192996994294239_concrete_of_code s₀ s₉ →
  Spec A_block_6359192996994294239 s₀ s₉ := by
  unfold block_6359192996994294239_concrete_of_code A_block_6359192996994294239
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma block_6359192996994294239_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_6359192996994294239 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    exact h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have hs1 : isOk s₁ := fun_uncheckedInc_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hstok : isOk (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧) := by
    simpa only [isOk_setEvm] using hs1
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hstok h2nf (Spec_ok_unfold hstok h2nf h₂)
  have hs3 : isOk s₃ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  simpa [isOk_insert] using hs3

lemma block_6359192996994294239_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_6359192996994294239 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_6359192996994294239_isOk hok hnf h)

/-! ### Growing the tree, step one

`_1` raises the stored height by one and then reads the default node for the new level.
The height lives at slot 0, so unlike everything on the update path this block DOES write a
constant-numbered slot -- deliberately.  Its frame therefore says "slot 0 and nothing else",
not "no low slot at all". -/

/-- **KECCAK WINDOW.**  An `sstore`, a subtraction, and one accessor hash. -/
lemma block_6359192996994294239_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_block_6359192996994294239 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := fun_uncheckedInc_isOk h1nf a₁
  have h1e : s₁.evm = s₀.evm := fun_uncheckedInc_evm hok h1nf a₁
  have hstok : isOk (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hs1
  have hste : (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧).evm
      = Clear.EVMState.sstore s₀.evm 0 (s₁["expr"]!!) := by
    rw [Clear.evm_setEvm_of_isOk hs1, h1e]
  have a₂ := Spec_ok_unfold hstok h2nf h₂
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hstok h2nf a₂
  obtain ⟨hR2, hC2⟩ := checked_sub_uint256_config hstok h2nf
    (by rw [hste]; exact Clear.StorageFrame.rangeInWindow_sstore hR)
    (by rw [hste]; exact Clear.StorageFrame.cachedInWindow_sstore hC) a₂
  obtain ⟨hR3, hC3⟩ := storage_array_index_access_bytes32_dyn_ptr_config hs2 h3nf hR2 hC2
    (Spec_ok_unfold hs2 h3nf h₃)
  simpa only [evm_insert] using ⟨hR3, hC3⟩

/-- **CLEAN FLAG, BACKWARDS.**  The accessor hashes, so this runs the one direction. -/
lemma block_6359192996994294239_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_6359192996994294239 s₀ s₉) : Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf hclean
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := fun_uncheckedInc_isOk h1nf a₁
  have h1e : s₁.evm = s₀.evm := fun_uncheckedInc_evm hok h1nf a₁
  have hstok : isOk (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hs1
  have a₂ := Spec_ok_unfold hstok h2nf h₂
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hstok h2nf a₂
  rw [evm_insert] at hclean
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    storage_array_index_access_bytes32_dyn_ptr_clean hs2 h3nf hclean
      (Spec_ok_unfold hs2 h3nf h₃)
  have c1 := (checked_sub_uint256_clean hstok h2nf a₂).mp c2
  rw [Clear.evm_setEvm_of_isOk hs1, Clear.KeccakClean.clean_sstore, h1e] at c1
  exact c1

/-- **STORAGE FRAME: SLOT 0 AND NOTHING ELSE.**

This block raises the height, which is a constant-numbered slot -- so it cannot claim to
preserve low slots outright.  What it does preserve is every OTHER slot: the increment and
the subtraction write nothing, and the accessor only computes an address.

That is what the leaf counter needs.  Slot 1 is not slot 0, so the count survives the
growth path even though the height does not. -/
lemma block_6359192996994294239_sload_of_ne {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hc0 : c ≠ 0)
    (h : A_block_6359192996994294239 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := fun_uncheckedInc_isOk h1nf a₁
  have h1e : s₁.evm = s₀.evm := fun_uncheckedInc_evm hok h1nf a₁
  have hstok : isOk (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hs1
  have a₂ := Spec_ok_unfold hstok h2nf h₂
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hstok h2nf a₂
  rw [evm_insert,
    storage_array_index_access_bytes32_dyn_ptr_sload hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃),
    checked_sub_uint256_sload hstok h2nf a₂, Clear.evm_setEvm_of_isOk hs1,
    Clear.KeccakDistinct.sload_sstore_of_ne _ hc0, h1e]

/-- **FRAME.**  The height bump moves `expr`, the subtraction's `split_expr_2`, the
accessor's `_3`/`_4`, and the loaded `split_expr_3`.  Everything else crosses. -/
lemma block_6359192996994294239_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hve : v ≠ "expr") (hv2 : v ≠ "split_expr_2") (hv3 : v ≠ "_3") (hv4 : v ≠ "_4")
    (hv5 : v ≠ "split_expr_3")
    (h : A_block_6359192996994294239 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := fun_uncheckedInc_isOk h1nf a₁
  have hstok : isOk (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hs1
  have a₂ := Spec_ok_unfold hstok h2nf h₂
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hstok h2nf a₂
  rw [lookup_insert_of_ne hv5,
    storage_array_index_access_bytes32_dyn_ptr_frame hs2 h3nf hv3 hv4
      (Spec_ok_unfold hs2 h3nf h₃),
    checked_sub_uint256_frame hstok h2nf hv2 a₂, Clear.lookup_setEvm hs1,
    fun_uncheckedInc_frame hok h1nf hve a₁]

end

end L2InteropCommitmentTree.Common
