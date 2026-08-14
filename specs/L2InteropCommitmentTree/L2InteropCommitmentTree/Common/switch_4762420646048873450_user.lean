import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7746411058724286464
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_896716371604423710
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_4354665484259437184
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_4762420646048873450_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The parity dispatch** — one level of the Merkle fold, choosing the sibling's side.

`split_expr_5` is `mod_uint256(var_index)`, so it is nonzero exactly when the index is
ODD.  The two branches differ in more than which sibling they read:

- odd (`split_expr_5 ≠ 0`): the node is a RIGHT child.  Read the neighbour at
  `index - 1` and hash `(sibling, currentHash)`.
- even (default): the node is a LEFT child.  Select the sibling via
  `switch_4354665484259437184` — the neighbour at `index + 1`, or the level's empty default — and hash `(currentHash, sibling)`.

So the running hash is the RIGHT argument when the node is a right child and the LEFT
argument when it is a left child.  That ordering is what makes the recomputed root
agree with the tree's; swapping it would silently produce a different root for the
same leaves. -/
def A_switch_4762420646048873450 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_7746411058724286464 s₀ s₁ ∧
    ∃ s₂, Spec A_block_896716371604423710 s₁ s₂ ∧
      ∃ s₃, Spec A_switch_4354665484259437184 (s₀⟦"expr" ↦ 0⟧) s₃ ∧
        ∃ s₄, Spec (A_fun_efficientHash "var_currentHash"
            (s₃["var_currentHash"]!!) (s₃["expr"]!!)) s₃ s₄ ∧
          ((s₀["split_expr_6"]!! = 0 → s₉ = s₄) ∧
           (s₀["split_expr_6"]!! ≠ 0 → s₉ = s₂))

lemma switch_4762420646048873450_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4762420646048873450_concrete_of_code s₀ s₉ →
  Spec A_switch_4762420646048873450 s₀ s₉ := by
  unfold switch_4762420646048873450_concrete_of_code A_switch_4762420646048873450
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
lemma switch_4762420646048873450_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_4762420646048873450 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heven, hodd⟩ := h
  by_cases he : s₀["split_expr_6"]!! = 0
  · rw [heven he] at hnf ⊢
    have h3nf : ¬ ❓ s₃ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
    have hexpr : isOk (s₀⟦"expr" ↦ 0⟧) := by simpa [isOk_insert] using hok
    have hs3 : isOk s₃ :=
      switch_4354665484259437184_isOk hexpr h3nf (Spec_ok_unfold hexpr h3nf h₃)
    exact fun_efficientHash_isOk hs3 (Spec_ok_unfold hs3 hnf h₄)
  · rw [hodd he] at hnf ⊢
    have h1nf : ¬ ❓ s₁ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
    have hs1 : isOk s₁ := block_7746411058724286464_isOk hok h1nf (Spec_ok_unfold hok h1nf h₁)
    exact block_896716371604423710_isOk hs1 hnf (Spec_ok_unfold hs1 hnf h₂)

lemma switch_4762420646048873450_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_4762420646048873450 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (switch_4762420646048873450_isOk hok hnf h)


/-- **FRAME.**  The parity switch folds one level into `var_currentHash` and touches
nothing else -- in particular not `var_index` or `var_i`.  Generic-slot copy, so the
output list carries the extra `split_expr_12` the zero-hash branch computes. -/
lemma switch_4762420646048873450_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hv : v ∉ (["_6", "_7", "split_expr_7", "_8", "_9", "split_expr_8", "split_expr_9",
      "var_currentHash", "_10", "_11", "split_expr_10", "_12", "_13", "split_expr_11",
      "split_expr_12", "_14", "_15", "split_expr_13", "expr"] : List Identifier))
    (h : A_switch_4762420646048873450 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨h6, h7, hsub, h8, h9, hld, hout, hcur, h10, h11, hadd, h12, h13, hld11,
    hdd, h14, h15, hld13, hexpr⟩ := hv
  have hL5648 : v ∉ (["_6", "_7", "split_expr_7", "_8", "_9", "split_expr_8",
      "split_expr_9"] : List Identifier) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h6, h7, hsub, h8, h9, hld, hout⟩
  have hL2003 : v ∉ (["_10", "_11", "split_expr_10", "_12", "_13", "split_expr_11",
      "split_expr_12", "_14", "_15", "split_expr_13", "expr"] : List Identifier) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h10, h11, hadd, h12, h13, hld11, hdd, h14, h15, hld13, hexpr⟩
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, hbrEven, hbrOdd⟩ := h
  by_cases hc : s₀["split_expr_6"]!! = 0
  · rw [hbrEven hc] at hnf ⊢
    have hins : isOk (s₀⟦"expr" ↦ 0⟧) := isOk_insert.mpr hok
    have h3nf : ¬ ❓ s₃ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
    have hs3 : isOk s₃ :=
      switch_4354665484259437184_isOk hins h3nf (Spec_ok_unfold hins h3nf h₃)
    have e4 : s₄[v]!! = s₃[v]!! :=
      fun_efficientHash_frame hs3 hnf hcur (Spec_ok_unfold hs3 hnf h₄)
    have e3 : s₃[v]!! = (s₀⟦"expr" ↦ 0⟧)[v]!! :=
      switch_4354665484259437184_frame hins h3nf hL2003 (Spec_ok_unfold hins h3nf h₃)
    rw [e4, e3, lookup_insert_of_ne hexpr]
  · rw [hbrOdd hc] at hnf ⊢
    have h1nf : ¬ ❓ s₁ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
    have hs1 : isOk s₁ :=
      block_7746411058724286464_isOk hok h1nf (Spec_ok_unfold hok h1nf h₁)
    have e2 : s₂[v]!! = s₁[v]!! :=
      block_896716371604423710_frame hs1 hnf hcur (Spec_ok_unfold hs1 hnf h₂)
    have e1 : s₁[v]!! = s₀[v]!! :=
      block_7746411058724286464_frame hok h1nf hL5648 (Spec_ok_unfold hok h1nf h₁)
    rw [e2, e1]

end

end L2InteropCommitmentTree.Common
