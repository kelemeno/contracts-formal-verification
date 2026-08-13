import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5648918763415424361
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1432253982873054235
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_2003501192971474853
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_8961670722464898128_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The parity dispatch** — one level of the Merkle fold, choosing the sibling's side.

`split_expr_5` is `mod_uint256(var_index)`, so it is nonzero exactly when the index is
ODD.  The two branches differ in more than which sibling they read:

- odd (`split_expr_5 ≠ 0`): the node is a RIGHT child.  Read the neighbour at
  `index - 1` and hash `(sibling, currentHash)`.
- even (default): the node is a LEFT child.  Select the sibling via
  `switch_2003501192971474853` — the neighbour at `index + 1`, or the level's empty
  default at the right edge — and hash `(currentHash, sibling)`.

So the running hash is the RIGHT argument when the node is a right child and the LEFT
argument when it is a left child.  That ordering is what makes the recomputed root
agree with the tree's; swapping it would silently produce a different root for the
same leaves. -/
def A_switch_8961670722464898128 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_5648918763415424361 s₀ s₁ ∧
    ∃ s₂, Spec A_block_1432253982873054235 s₁ s₂ ∧
      ∃ s₃, Spec A_switch_2003501192971474853 (s₀⟦"expr" ↦ 0⟧) s₃ ∧
        ∃ s₄, Spec (A_fun_efficientHash "var_currentHash"
            (s₃["var_currentHash"]!!) (s₃["expr"]!!)) s₃ s₄ ∧
          ((s₀["split_expr_5"]!! = 0 → s₉ = s₄) ∧
           (s₀["split_expr_5"]!! ≠ 0 → s₉ = s₂))

lemma switch_8961670722464898128_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8961670722464898128_concrete_of_code s₀ s₉ →
  Spec A_switch_8961670722464898128 s₀ s₉ := by
  unfold switch_8961670722464898128_concrete_of_code A_switch_8961670722464898128
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

end

end L2InteropCommitmentTree.Common
