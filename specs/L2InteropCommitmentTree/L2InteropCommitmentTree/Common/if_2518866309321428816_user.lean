import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6359192996994294239
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3221258955042269759
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5267003775473151689
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2518866309321428816_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The grow-a-level branch**: `if eq(_1, split_expr_1) { … }`.

Taken when the leaf count `_1` has reached the tree's capacity `split_expr_1 = 1 << levels`
-- i.e. the tree is exactly full -- and it runs the three growth blocks in order: bump the
level count and read the old top default, hash that default with itself and append it to
the defaults array, then give the new level a one-node array holding the same value.

Note the condition is EQUALITY, not `≥`: the check happens on every insertion, so the
count can only ever arrive at capacity exactly. -/
def A_if_2518866309321428816 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_6359192996994294239 s₀ s₁ ∧
    ∃ s₂, Spec A_block_3221258955042269759 s₁ s₂ ∧
      ∃ s₃, Spec A_block_5267003775473151689 s₂ s₃ ∧
        ((s₀["_1"]!! = s₀["split_expr_1"]!! → s₉ = s₃) ∧
         (s₀["_1"]!! ≠ s₀["split_expr_1"]!! → s₉ = s₀))

lemma if_2518866309321428816_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2518866309321428816_concrete_of_code s₀ s₉ →
  Spec A_if_2518866309321428816 s₀ s₉ := by
  unfold if_2518866309321428816_concrete_of_code A_if_2518866309321428816
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  refine ⟨s₁, h₁, s₂, h₂, s₃, h₃, ?_, ?_⟩
  · intro hg
    rw [if_pos hg] at heq
    exact heq.symm
  · intro hg
    rw [if_neg hg] at heq
    exact heq.symm


/-- **NO HEIGHT GROWTH: the state is unchanged.**

`pushNewLeaf` grows the tree's height only when the new index exactly fills the current
capacity (`index == 1 << height`).  Off that path this branch is the identity, so every
level array keeps its length -- `TreeLayout.LevelsSized` is preserved for free.

That is the common case: one leaf in `2 ^ height` triggers growth. -/
lemma if_2518866309321428816_id_of_ne {s₀ s₉ : State}
    (hne : s₀["_1"]!! ≠ s₀["split_expr_1"]!!)
    (h : A_if_2518866309321428816 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨_, _, _, _, _, _, _, hneg⟩ := h
  exact hneg hne

/-! ### The capacity guard

When the tree is full, grow it: raise the height (slot 0), push a new default (slot 3),
push a new level array (slot 2).  Each block names the slot it deliberately writes, so the
guard can say precisely what moves.

The pieces had to be assembled in a particular order.  The window frames of blocks two and
three want array-length bounds at `s₁` and `s₂`, which come from the storage frames of the
blocks before them, which need the flag -- so the flag had to become free of size
hypotheses first (`array_push_clean_unconditional` and its nested cousin) before any of
this could be stated. -/

private lemma cap_nf {s₀ s₉ : State} (hnf : ¬ ❓ s₉) {s₁ s₂ s₃ : State}
    (h₂ : Spec A_block_3221258955042269759 s₁ s₂)
    (h₃ : Spec A_block_5267003775473151689 s₂ s₃)
    (hyes : s₀["_1"]!! = s₀["split_expr_1"]!! → s₉ = s₃)
    (hg : s₀["_1"]!! = s₀["split_expr_1"]!!) : ¬ ❓ s₃ ∧ ¬ ❓ s₂ ∧ ¬ ❓ s₁ := by
  have h3nf : ¬ ❓ s₃ := by rw [hyes hg] at hnf; exact hnf
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  exact ⟨h3nf, h2nf, fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)⟩

set_option maxHeartbeats 1600000 in
/-- **THE GROWTH PATH MOVES SLOTS 0, 2 AND 3 -- AND NOTHING ELSE.**

Which is what the leaf counter needs: slot 1 is none of the three, so the count survives a
capacity growth.

`hfits`/`hlen` are the standing address-arithmetic assumptions of this path -- no array is
near `2 ^ 64` entries, none reaches `2 ^ 32`.  As always they are about the element address
`keccak(array) + index` wrapping onto a low slot, not about any bounds check. -/
lemma if_2518866309321428816_sload_of_ne {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hc0 : c ≠ 0) (hc2 : c ≠ 2) (hc3 : c ≠ 3)
    (hclow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hfits : ∀ q : Literal, Clear.EVMState.sload s₀.evm q < 18446744073709551616)
    (hlen : ∀ q : Literal,
      (Clear.EVMState.sload s₀.evm q).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_if_2518866309321428816 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, hyes, hno⟩ := h
  by_cases hg : s₀["_1"]!! = s₀["split_expr_1"]!!
  · obtain ⟨h3nf, h2nf, h1nf⟩ := cap_nf hnf h₂ h₃ hyes hg
    rw [hyes hg] at hclean ⊢
    have a₁ := Spec_ok_unfold hok h1nf h₁
    have hs1 : isOk s₁ := block_6359192996994294239_isOk hok h1nf a₁
    obtain ⟨hR1, hC1⟩ := block_6359192996994294239_config hok h1nf hR hC a₁
    have a₂ := Spec_ok_unfold hs1 h2nf h₂
    have hs2 : isOk s₂ := block_3221258955042269759_isOk hs1 h2nf a₂
    -- the height write moves slot 0 only, so slots 2 and 3 reach block two unchanged
    have hsl1 : ∀ q : Literal, q ≠ 0 →
        Clear.EVMState.sload s₁.evm q = Clear.EVMState.sload s₀.evm q :=
      fun q hq => block_6359192996994294239_sload_of_ne hok h1nf hq a₁
    -- the flag first: it costs nothing now, and the storage frames below need it
    have c2 : Clear.KeccakClean.Clean s₂.evm :=
      block_5267003775473151689_clean hs2 h3nf hclean (Spec_ok_unfold hs2 h3nf h₃)
    have c1 : Clear.KeccakClean.Clean s₁.evm :=
      block_3221258955042269759_clean hs1 h2nf c2 a₂
    -- block two moves slot 3 only
    have hsl2 : ∀ q : Literal, q ≠ 3 → q.val < Clear.KeccakInjective.lowSlotBound →
        Clear.EVMState.sload s₂.evm q = Clear.EVMState.sload s₁.evm q := by
      intro q hq hlow
      exact block_3221258955042269759_sload_of_ne hs1 h2nf
        (by rw [hsl1 3 (by decide)]; exact hfits 3) hq hlow
        (by rw [hsl1 3 (by decide)]; exact hlen 3) hR1 hC1 c2 a₂
    obtain ⟨hR2, hC2⟩ := block_3221258955042269759_config hs1 h2nf
      (by rw [hsl1 3 (by decide)]; exact hfits 3) hR1 hC1 a₂
    -- block three moves slot 2 only
    rw [block_5267003775473151689_sload_of_ne hs2 h3nf
        (by rw [hsl2 2 (by decide) (by show (2:ℕ) < 2^32; norm_num), hsl1 2 (by decide)]
            exact hfits 2)
        hc2 hclow
        (by rw [hsl2 2 (by decide) (by show (2:ℕ) < 2^32; norm_num), hsl1 2 (by decide)]
            exact hlen 2)
        hR2 hC2 hclean (Spec_ok_unfold hs2 h3nf h₃),
      hsl2 c hc3 hclow, hsl1 c hc0]
  · rw [hno hg]

/-- **FRAME.**  Growing the tree touches ten scratch bindings and no others.  Notably `_1`,
the leaf count read before the guard, is not among them -- which is what lets a caller
track the count THROUGH a growth rather than only around it. -/
lemma if_2518866309321428816_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hv : v ∉ (["expr", "split_expr_2", "_3", "_4", "split_expr_3", "_5", "expr_1",
      "size", "_6", "expr_mpos"] : List Identifier))
    (h : A_if_2518866309321428816 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨he, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hv
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, hyes, hno⟩ := h
  by_cases hg : s₀["_1"]!! = s₀["split_expr_1"]!!
  · obtain ⟨h3nf, h2nf, h1nf⟩ := cap_nf hnf h₂ h₃ hyes hg
    rw [hyes hg]
    have a₁ := Spec_ok_unfold hok h1nf h₁
    have hs1 : isOk s₁ := block_6359192996994294239_isOk hok h1nf a₁
    have a₂ := Spec_ok_unfold hs1 h2nf h₂
    have hs2 : isOk s₂ := block_3221258955042269759_isOk hs1 h2nf a₂
    rw [block_5267003775473151689_frame hs2 h3nf h9 h8 h10 (Spec_ok_unfold hs2 h3nf h₃),
      block_3221258955042269759_frame hs1 h2nf h6 h7 h8 h9 a₂,
      block_6359192996994294239_frame hok h1nf he h2 h3 h4 h5 a₁]
  · rw [hno hg]

lemma if_2518866309321428816_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2518866309321428816 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, hyes, hno⟩ := h
  by_cases hg : s₀["_1"]!! = s₀["split_expr_1"]!!
  · obtain ⟨h3nf, h2nf, h1nf⟩ := cap_nf hnf h₂ h₃ hyes hg
    rw [hyes hg]
    have hs1 : isOk s₁ := block_6359192996994294239_isOk hok h1nf (Spec_ok_unfold hok h1nf h₁)
    have hs2 : isOk s₂ :=
      block_3221258955042269759_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
    exact block_5267003775473151689_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
  · rw [hno hg]; exact hok

set_option maxHeartbeats 1600000 in
/-- **KECCAK WINDOW.**  Each block keeps it; the size bounds come from the storage frames
of the blocks before, which is why this could not be stated before those existed. -/
lemma if_2518866309321428816_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : ∀ q : Literal, Clear.EVMState.sload s₀.evm q < 18446744073709551616)
    (hlen : ∀ q : Literal,
      (Clear.EVMState.sload s₀.evm q).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_if_2518866309321428816 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, hyes, hno⟩ := h
  by_cases hg : s₀["_1"]!! = s₀["split_expr_1"]!!
  · obtain ⟨h3nf, h2nf, h1nf⟩ := cap_nf hnf h₂ h₃ hyes hg
    rw [hyes hg] at hclean ⊢
    have a₁ := Spec_ok_unfold hok h1nf h₁
    have hs1 : isOk s₁ := block_6359192996994294239_isOk hok h1nf a₁
    obtain ⟨hR1, hC1⟩ := block_6359192996994294239_config hok h1nf hR hC a₁
    have a₂ := Spec_ok_unfold hs1 h2nf h₂
    have hs2 : isOk s₂ := block_3221258955042269759_isOk hs1 h2nf a₂
    have hsl1 : ∀ q : Literal, q ≠ 0 →
        Clear.EVMState.sload s₁.evm q = Clear.EVMState.sload s₀.evm q :=
      fun q hq => block_6359192996994294239_sload_of_ne hok h1nf hq a₁
    have c2 : Clear.KeccakClean.Clean s₂.evm :=
      block_5267003775473151689_clean hs2 h3nf hclean (Spec_ok_unfold hs2 h3nf h₃)
    have hsl2 : ∀ q : Literal, q ≠ 3 → q.val < Clear.KeccakInjective.lowSlotBound →
        Clear.EVMState.sload s₂.evm q = Clear.EVMState.sload s₁.evm q := by
      intro q hq hlow
      exact block_3221258955042269759_sload_of_ne hs1 h2nf
        (by rw [hsl1 3 (by decide)]; exact hfits 3) hq hlow
        (by rw [hsl1 3 (by decide)]; exact hlen 3) hR1 hC1 c2 a₂
    obtain ⟨hR2, hC2⟩ := block_3221258955042269759_config hs1 h2nf
      (by rw [hsl1 3 (by decide)]; exact hfits 3) hR1 hC1 a₂
    exact block_5267003775473151689_config hs2 h3nf
      (by rw [hsl2 2 (by decide) (by show (2:ℕ) < 2^32; norm_num), hsl1 2 (by decide)]
          exact hfits 2)
      hR2 hC2 (Spec_ok_unfold hs2 h3nf h₃)
  · rw [hno hg]; exact ⟨hR, hC⟩

end

end L2InteropCommitmentTree.Common
