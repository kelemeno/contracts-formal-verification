import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3711784909988835814_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Copy level `i`'s node from one array into the other.**

```
    _7, _8  := storage_array_index_access(2, var_i)     -- destination array, slot 2
    _9, _10 := storage_array_index_access(3, var_i)     -- source array, slot 3
    split_expr_7 := sload(_9)
    split_expr_8 := extract_from_storage_value_dynamict_bytes32(split_expr_7, _10)
    array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr(_7, split_expr_8)
```

Both array slots are LITERALS (2 and 3), so the loop cannot be steered onto another
array: the only caller-influenced quantity is the level index `var_i`, and both
accesses are bounds-checked against their own array's length.  The value pushed is
the one just read from the source array at the same index. -/
def A_block_3711784909988835814 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_7" "_8" 2 (s₀["var_i"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_9" "_10" 3 (s₁["var_i"]!!)) s₁ s₂ ∧
      (let ld := s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧
       ∃ s₃, Spec (A_extract_from_storage_value_dynamict_bytes32 "split_expr_8"
           (ld["split_expr_7"]!!) (ld["_10"]!!)) ld s₃ ∧
         ∃ s₄, Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
             (s₃["_7"]!!) (s₃["split_expr_8"]!!)) s₃ s₄ ∧
           s₉ = s₄)

lemma block_3711784909988835814_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3711784909988835814_concrete_of_code s₀ s₉ →
  Spec A_block_3711784909988835814 s₀ s₉ := by
  unfold block_3711784909988835814_concrete_of_code A_block_3711784909988835814
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, rest⟩ := hc
  exact ⟨s₁, h₁, by
    obtain ⟨s₂, h₂, rest2⟩ := rest
    exact ⟨s₂, h₂, by
      first
        | exact rest2.symm
        | (obtain ⟨s₃, h₃, s₄, h₄, heq⟩ := rest2; exact ⟨s₃, h₃, s₄, h₄, heq.symm⟩)⟩⟩

/-- Output is `Ok`: four function returns in sequence, `hnf` walked backwards. -/
lemma block_3711784909988835814_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3711784909988835814 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    exact h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
      (by simpa [isOutOfFuel_insert'] using hoo))
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hld : isOk (s₂⟦"split_expr_7" ↦ Clear.EVMState.sload s₂.evm (s₂["_9"]!!)⟧) := by
    simpa [isOk_insert] using hs2
  have hs3 : isOk s₃ :=
    extract_from_storage_value_dynamict_bytes32_isOk h3nf (Spec_ok_unfold hld h3nf h₃)
  exact array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk hnf
    (Spec_ok_unfold hs3 hnf h₄)

lemma block_3711784909988835814_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3711784909988835814 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_3711784909988835814_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
