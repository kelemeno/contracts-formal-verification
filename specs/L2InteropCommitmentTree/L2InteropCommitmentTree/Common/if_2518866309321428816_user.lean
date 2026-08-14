import Clear.ReasoningPrinciple
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

end

end L2InteropCommitmentTree.Common
