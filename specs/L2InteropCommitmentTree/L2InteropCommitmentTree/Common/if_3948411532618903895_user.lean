import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5765234204941653661
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3948411532618903895_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The copy-up branch**: `if iszero(split_expr_4) { … }`.

Sets `oldMaxNodeNumber := checked_sub_uint256(_1)` and `maxNodeNumber := _1`, zeroes the
level counter, and runs the level walk -- the loop that copies each level's node from one
array into the other, halving both counts as it climbs.

The two counts start one apart (`_1 - 1` and `_1`), which is what the loop's second break
condition tests: they meet exactly when the old tree's levels are exhausted.  The loop
enters through its postcondition `AFor_for_5765234204941653661`. -/
def A_if_3948411532618903895 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_checked_sub_uint256 "var_oldMaxNodeNumber" (s₀["_1"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec AFor_for_5765234204941653661
        (s₁⟦"var_maxNodeNumber" ↦ s₁["_1"]!!⟧⟦"var_i" ↦ 0⟧⟦"var_i" ↦ 0⟧) s₂ ∧
      ((s₀["split_expr_4"]!! = 0 → s₉ = s₂) ∧
       (s₀["split_expr_4"]!! ≠ 0 → s₉ = s₀))

lemma if_3948411532618903895_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3948411532618903895_concrete_of_code s₀ s₉ →
  Spec A_if_3948411532618903895 s₀ s₉ := by
  unfold if_3948411532618903895_concrete_of_code A_if_3948411532618903895
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

end

end L2InteropCommitmentTree.Common
