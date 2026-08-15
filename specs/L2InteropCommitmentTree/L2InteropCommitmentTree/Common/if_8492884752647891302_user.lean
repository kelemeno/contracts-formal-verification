import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_2693611967757691411
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8492884752647891302_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The copy-up branch**: `if iszero(split_expr_4) { … }`.

Sets `oldMaxNodeNumber := checked_sub_uint256(_1)` and `maxNodeNumber := _1`, zeroes the
level counter, and runs the level walk -- the loop that copies each level's node from one
array into the other, halving both counts as it climbs.

The two counts start one apart (`_1 - 1` and `_1`), which is what the loop's second break
condition tests: they meet exactly when the old tree's levels are exhausted.  The loop
enters through its postcondition `AFor_for_2693611967757691411`. -/
def A_if_8492884752647891302 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_checked_sub_uint256 "var_oldMaxNodeNumber" (s₀["_1"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec AFor_for_2693611967757691411
        (s₁⟦"var_maxNodeNumber" ↦ s₁["_1"]!!⟧⟦"var_i" ↦ 0⟧⟦"var_i" ↦ 0⟧) s₂ ∧
      ((s₀["split_expr_4"]!! = 0 → s₉ = s₂) ∧
       (s₀["split_expr_4"]!! ≠ 0 → s₉ = s₀))

lemma if_8492884752647891302_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8492884752647891302_concrete_of_code s₀ s₉ →
  Spec A_if_8492884752647891302 s₀ s₉ := by
  unfold if_8492884752647891302_concrete_of_code A_if_8492884752647891302
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  refine ⟨s₁, h₁, s₂, h₂, ?_, ?_⟩
  · intro hg
    rw [if_pos hg] at heq
    exact heq.symm
  · intro hg
    rw [if_neg hg] at heq
    exact heq.symm


/-- **NO LEVEL GROWTH: the state is unchanged.**

The level-growing loop runs only when the new index is non-zero (`split_expr_4` is
`decide (_1 = 0)`).  For the very first leaf the branch is the identity, so the level arrays
are untouched and `TreeLayout.LevelsSized` is preserved.

The other path runs `for_2693611967757691411`, which is where the arrays actually grow --
that is the part still to be proved. -/
lemma if_8492884752647891302_id_of_ne {s₀ s₉ : State}
    (hne : s₀["split_expr_4"]!! ≠ 0)
    (h : A_if_8492884752647891302 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨_, _, _, _, _, hneg⟩ := h
  exact hneg hne

/-- **CLEAN FLAG, BACKWARDS, ACROSS THE DEPTH EXTENSION.**

The guard either does nothing or runs the checked subtraction and the whole level-copy
loop.  Both halves now carry the flag: `checked_sub` as an iff, the loop through the
conjunct its induction proves.

`hok9` is what rules the loop's own break arms in or out -- the loop's `AFor` states its
clean conjunct under `isOk`, and an `Ok` result at this level is exactly that witness. -/
lemma if_8492884752647891302_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hok9 : isOk s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_if_8492884752647891302 s₀ s₉) : Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, hpos, hneg⟩ := h
  by_cases hc : s₀["split_expr_4"]!! = 0
  · -- the extension ran
    have he : s₉ = s₂ := hpos hc
    have h2nf : ¬ ❓ s₂ := by rw [he] at hnf; exact hnf
    have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_insert'] using hoo))
    have a₁ := Spec_ok_unfold hok h1nf h₁
    have hs1 : isOk s₁ := checked_sub_uint256_isOk hok h1nf a₁
    have hinok : isOk ((s₁⟦"var_maxNodeNumber" ↦ s₁["_1"]!!⟧⟦"var_i" ↦ 0⟧)⟦"var_i" ↦ 0⟧) :=
      isOk_insert.mpr (isOk_insert.mpr (isOk_insert.mpr hs1))
    have a₂ := Spec_ok_unfold hinok h2nf h₂
    rw [he] at hclean hok9
    have cin := a₂.2 hok9 hclean
    simp only [evm_insert] at cin
    exact (checked_sub_uint256_clean hok h1nf a₁).mp cin
  · rw [hneg hc] at hclean
    exact hclean

end

end L2InteropCommitmentTree.Common
