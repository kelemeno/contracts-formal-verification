import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_3698598331043311763_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The even-index sibling, generic-tree variant.**

Same rule as `switch_2003501192971474853` -- neighbour at `index + 1`, or the level's
empty default at the right edge -- but for the copy of the tree whose storage location
is a parameter.  Two things follow from that:

- the level array is the local `_1` rather than the literal slot 2;
- the DEFAULTS array is at `var_self_slot + 3`, computed here rather than being the
  literal slot 3.  So the layout is: the tree struct's own slot, and the defaults three
  slots past it.

The right-edge case is the one that matters for soundness: with no neighbour to hash
against, the fold uses the precomputed empty-subtree hash for that level, which is what
makes a partially-filled level produce the same root as the abstract tree. -/
def A_switch_3698598331043311763 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_10" "_11" (s₀["_1"]!!) (s₀["var_i"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_checked_add_uint256 "split_expr_10" (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_12" "_13" (s₂["_10"]!!) (s₂["split_expr_10"]!!)) s₂ s₃ ∧
        (let ld := s₃⟦"split_expr_11" ↦ Clear.EVMState.sload s₃.evm (s₃["_12"]!!)⟧
         ∃ s₄, Spec (A_extract_from_storage_value_dynamict_bytes32 "expr" (ld["split_expr_11"]!!) (ld["_13"]!!)) ld s₄ ∧
           (let dd := s₀⟦"split_expr_12" ↦ s₀["var_self_slot"]!! + 3⟧
            ∃ s₅, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_14" "_15" (dd["split_expr_12"]!!) (dd["var_i"]!!)) dd s₅ ∧
              (let ld2 := s₅⟦"split_expr_13" ↦ Clear.EVMState.sload s₅.evm (s₅["_14"]!!)⟧
               ∃ s₆, Spec (A_extract_from_storage_value_dynamict_bytes32 "expr" (ld2["split_expr_13"]!!) (ld2["_15"]!!)) ld2 s₆ ∧
                 ((s₀["var_maxNodeNumber"]!! = s₀["var_index"]!! → s₉ = s₆) ∧
                  (s₀["var_maxNodeNumber"]!! ≠ s₀["var_index"]!! → s₉ = s₄)))))

lemma switch_3698598331043311763_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_3698598331043311763_concrete_of_code s₀ s₉ →
  Spec A_switch_3698598331043311763 s₀ s₉ := by
  unfold switch_3698598331043311763_concrete_of_code A_switch_3698598331043311763
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, heq⟩ := hc
  refine ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, ?_, ?_⟩
  · intro hedge
    rw [← heq]
    simp [hedge]
  · intro hne
    rw [← heq]
    simp [hne]

/-- Output is `Ok` on either branch; each branch is its own chain of function returns. -/
lemma switch_3698598331043311763_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_3698598331043311763 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, s₆, h₆, hedge, hne⟩ := h
  by_cases he : s₀["var_maxNodeNumber"]!! = s₀["var_index"]!!
  · rw [hedge he] at hnf ⊢
    have h5nf : ¬ ❓ s₅ := by
      intro hoo
      exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₆
        (by simpa [isOutOfFuel_insert'] using hoo))
    have hdd : isOk (s₀⟦"split_expr_12" ↦ s₀["var_self_slot"]!! + 3⟧) := by
      simpa [isOk_insert] using hok
    have hs5 : isOk s₅ :=
      storage_array_index_access_bytes32_dyn__dyn_isOk h5nf (Spec_ok_unfold hdd h5nf h₅)
    have hld2 : isOk (s₅⟦"split_expr_13" ↦ Clear.EVMState.sload s₅.evm (s₅["_14"]!!)⟧) := by
      simpa [isOk_insert] using hs5
    exact extract_from_storage_value_dynamict_bytes32_isOk hnf (Spec_ok_unfold hld2 hnf h₆)
  · rw [hne he] at hnf ⊢
    have h3nf : ¬ ❓ s₃ := by
      intro hoo
      exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄
        (by simpa [isOutOfFuel_insert'] using hoo))
    have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
    have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
    have hs1 : isOk s₁ :=
      storage_array_index_access_bytes32_dyn__dyn_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
    have hs2 : isOk s₂ := checked_add_uint256_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      storage_array_index_access_bytes32_dyn__dyn_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hld : isOk (s₃⟦"split_expr_11" ↦ Clear.EVMState.sload s₃.evm (s₃["_12"]!!)⟧) := by
      simpa [isOk_insert] using hs3
    exact extract_from_storage_value_dynamict_bytes32_isOk hnf (Spec_ok_unfold hld hnf h₄)

lemma switch_3698598331043311763_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_3698598331043311763 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (switch_3698598331043311763_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
