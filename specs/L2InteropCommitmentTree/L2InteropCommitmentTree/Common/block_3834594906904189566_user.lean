import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3834594906904189566_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The odd-index sibling read**: the node at `index - 1` on level `i`.

```
    _5, _6 := storage_array_index_access(2, var_i)        -- level i's array
    split_expr_6 := checked_sub_uint256(var_index)        -- index - 1
    _7, _8 := storage_array_index_access(_5, split_expr_6)
    split_expr_8 := extract(sload(_7), _8)
```

An odd-indexed node is a RIGHT child, so its sibling is the node immediately to its
left and always exists — no default is needed, unlike the even case.  The decrement
is the checked one, so `index = 0` reverts rather than wrapping. -/
def A_block_3834594906904189566 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_5" "_6" 2 (s₀["var_i"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_checked_sub_uint256 "split_expr_6" (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_7" "_8"
          (s₂["_5"]!!) (s₂["split_expr_6"]!!)) s₂ s₃ ∧
        (let ld := s₃⟦"split_expr_7" ↦ Clear.EVMState.sload s₃.evm (s₃["_7"]!!)⟧
         ∃ s₄, Spec (A_extract_from_storage_value_dynamict_bytes32 "split_expr_8"
             (ld["split_expr_7"]!!) (ld["_8"]!!)) ld s₄ ∧
           s₉ = s₄)

lemma block_3834594906904189566_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3834594906904189566_concrete_of_code s₀ s₉ →
  Spec A_block_3834594906904189566 s₀ s₉ := by
  unfold block_3834594906904189566_concrete_of_code A_block_3834594906904189566
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq.symm⟩

lemma block_3834594906904189566_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3834594906904189566 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    exact hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ (by simpa [isOutOfFuel_insert'] using hoo))
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hs1 h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hld : isOk (s₃⟦"split_expr_7" ↦ Clear.EVMState.sload s₃.evm (s₃["_7"]!!)⟧) := by
    simpa [isOk_insert] using hs3
  exact extract_from_storage_value_dynamict_bytes32_isOk hnf (Spec_ok_unfold hld hnf h₄)

lemma block_3834594906904189566_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3834594906904189566 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_3834594906904189566_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
