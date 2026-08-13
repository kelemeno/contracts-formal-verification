import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3834594906904189566
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1432253982873054235
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_8987501505216042171
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_7836749200582770074_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The parity dispatch** — one level of the Merkle fold, choosing the sibling's side.

`split_expr_5` is `mod_uint256(var_index)`, so it is nonzero exactly when the index is
ODD.  The two branches differ in more than which sibling they read:

- odd (`split_expr_5 ≠ 0`): the node is a RIGHT child.  Read the neighbour at
  `index - 1` and hash `(sibling, currentHash)`.
- even (default): the node is a LEFT child.  Select the sibling via
  `switch_8987501505216042171` — the neighbour at `index + 1`, or the level's empty
  default at the right edge — and hash `(currentHash, sibling)`.

So the running hash is the RIGHT argument when the node is a right child and the LEFT
argument when it is a left child.  That ordering is what makes the recomputed root
agree with the tree's; swapping it would silently produce a different root for the
same leaves. -/
def A_switch_7836749200582770074 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_3834594906904189566 s₀ s₁ ∧
    ∃ s₂, Spec A_block_1432253982873054235 s₁ s₂ ∧
      ∃ s₃, Spec A_switch_8987501505216042171 (s₀⟦"expr" ↦ 0⟧) s₃ ∧
        ∃ s₄, Spec (A_fun_efficientHash "var_currentHash"
            (s₃["var_currentHash"]!!) (s₃["expr"]!!)) s₃ s₄ ∧
          ((s₀["split_expr_5"]!! = 0 → s₉ = s₄) ∧
           (s₀["split_expr_5"]!! ≠ 0 → s₉ = s₂))

lemma switch_7836749200582770074_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7836749200582770074_concrete_of_code s₀ s₉ →
  Spec A_switch_7836749200582770074 s₀ s₉ := by
  unfold switch_7836749200582770074_concrete_of_code A_switch_7836749200582770074
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hc
  refine ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, ?_, ?_⟩
  · intro heven
    rw [← heq]
    simp [heven]
  · intro hodd
    rw [← heq]
    simp [hodd]

/-- Output is `Ok` on either parity.  The odd branch ends in the hash block, the even
branch in `fun_efficientHash` -- both function returns. -/
lemma switch_7836749200582770074_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_7836749200582770074 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heven, hodd⟩ := h
  by_cases he : s₀["split_expr_5"]!! = 0
  · rw [heven he] at hnf ⊢
    have h3nf : ¬ ❓ s₃ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
    have hexpr : isOk (s₀⟦"expr" ↦ 0⟧) := by simpa [isOk_insert] using hok
    have hs3 : isOk s₃ :=
      switch_8987501505216042171_isOk hexpr h3nf (Spec_ok_unfold hexpr h3nf h₃)
    exact fun_efficientHash_isOk hs3 (Spec_ok_unfold hs3 hnf h₄)
  · rw [hodd he] at hnf ⊢
    have h1nf : ¬ ❓ s₁ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
    have hs1 : isOk s₁ := block_3834594906904189566_isOk hok h1nf (Spec_ok_unfold hok h1nf h₁)
    exact block_1432253982873054235_isOk hs1 hnf (Spec_ok_unfold hs1 hnf h₂)

lemma switch_7836749200582770074_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_7836749200582770074 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (switch_7836749200582770074_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
