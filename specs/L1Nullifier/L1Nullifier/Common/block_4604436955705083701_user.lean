import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_bool
import generated.L1Nullifier.L1Nullifier.cleanup_bool
import generated.L1Nullifier.L1Nullifier.require_helper_error_WithdrawalAlreadyFinalized
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749

import generated.L1Nullifier.L1Nullifier.Common.block_4604436955705083701_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

/-- **The replay check**: read the flag, negate it, require it, then derive the next slot.

```
    split_expr_8  := read_from_storage_split_offset_bool(split_expr_7)  -- the flag
    split_expr_9  := iszero(split_expr_8)                               -- NOT finalized?
    split_expr_10 := cleanup_bool(split_expr_9)                         -- normalise
    require_helper_error_WithdrawalAlreadyFinalized(split_expr_10)
    split_expr_11 := mapping_index_access_…_17749(_1)                   -- next mapping
```

So the guard fires exactly when the stored flag is NONZERO: `iszero` of it is 0, the
`require` sees 0, and the call reverts with `WithdrawalAlreadyFinalized()`.  A second
finalization of the same withdrawal therefore cannot proceed past this block -- which is
the deployed form of the no-replay property.

The read is masked to the low byte, so an unrelated field packed into the same slot
cannot make a cleared flag read back as set. -/
def A_block_4604436955705083701 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_read_from_storage_split_offset_bool "split_expr_8" (s₀["split_expr_7"]!!)) s₀ s₁ ∧
    (let neg := s₁⟦"split_expr_9" ↦ (decide (s₁["split_expr_8"]!! = 0)).toUInt256⟧
     ∃ s₂, Spec (A_cleanup_bool "split_expr_10" (neg["split_expr_9"]!!)) neg s₂ ∧
       ∃ s₃, Spec (A_require_helper_error_WithdrawalAlreadyFinalized
           (s₂["split_expr_10"]!!)) s₂ s₃ ∧
         ∃ s₄, Spec (A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749 "split_expr_11" (s₃["_1"]!!)) s₃ s₄ ∧
           s₉ = s₄)

lemma block_4604436955705083701_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4604436955705083701_concrete_of_code s₀ s₉ →
  Spec A_block_4604436955705083701 s₀ s₉ := by
  unfold block_4604436955705083701_concrete_of_code A_block_4604436955705083701
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq.symm⟩

lemma block_4604436955705083701_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_4604436955705083701 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    exact h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_insert'] using hoo))
  have hs1 : isOk s₁ :=
    read_from_storage_split_offset_bool_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hneg : isOk (s₁⟦"split_expr_9" ↦ (decide (s₁["split_expr_8"]!! = 0)).toUInt256⟧) := by
    simpa [isOk_insert] using hs1
  have hs2 : isOk s₂ := cleanup_bool_isOk h2nf (Spec_ok_unfold hneg h2nf h₂)
  have hs3 : isOk s₃ :=
    require_helper_error_WithdrawalAlreadyFinalized_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  exact mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749_isOk hnf (Spec_ok_unfold hs3 hnf h₄)

lemma block_4604436955705083701_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_4604436955705083701 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_4604436955705083701_isOk hok hnf h)

end

end L1Nullifier.Common
