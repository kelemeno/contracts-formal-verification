import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2743596091140315824_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Advance one level**: halve the index and the node count, then derive the slot of
the parent node.

```
    var_index         := checked_div_uint256(var_index)
    var_maxNodeNumber := checked_div_uint256(var_maxNodeNumber)
    split_expr_12     := checked_add_uint256(var_i)          -- next level
    _15, _16 := storage_array_index_access(2, split_expr_12) -- that level's array
    _17, _18 := storage_array_index_access(_15, var_index)   -- the node in it
```

Both the index and the count halve together, and the level index increments, so the
slot handed to the write block is the parent of the node just hashed.  The array at
slot 2 is a literal, so the level array cannot be redirected. -/
def A_block_2743596091140315824 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_checked_div_uint256 "var_index" (s₀["var_index"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_checked_div_uint256 "var_maxNodeNumber" (s₁["var_maxNodeNumber"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_checked_add_uint256 "split_expr_12" (s₂["var_i"]!!)) s₂ s₃ ∧
        ∃ s₄, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_15" "_16" 2
            (s₃["split_expr_12"]!!)) s₃ s₄ ∧
          ∃ s₅, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_17" "_18"
              (s₄["_15"]!!) (s₄["var_index"]!!)) s₄ s₅ ∧
            s₉ = s₅

lemma block_2743596091140315824_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2743596091140315824_concrete_of_code s₀ s₉ →
  Spec A_block_2743596091140315824 s₀ s₉ := by
  unfold block_2743596091140315824_concrete_of_code A_block_2743596091140315824
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩

lemma block_2743596091140315824_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2743596091140315824 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ := checked_add_uint256_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  have hs4 : isOk s₄ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h4nf (Spec_ok_unfold hs3 h4nf h₄)
  exact storage_array_index_access_bytes32_dyn__dyn_isOk hnf (Spec_ok_unfold hs4 hnf h₅)

lemma block_2743596091140315824_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2743596091140315824 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_2743596091140315824_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
