import Clear.ReasoningPrinciple
import specs.KeccakDistinct
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3221258955042269759_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Grow the tree by one level, part 2: the new level's empty default.**

```
    _5 := extract_from_storage_value_dynamict_bytes32(split_expr_3, _4)
    expr_1 := fun_efficientHash(_5, _5)                       -- hash(d, d)
    array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr(3, expr_1)
```

The default for a new level is the hash of the previous level's default WITH ITSELF --
the empty-subtree chain: an empty subtree one level up is two empty subtrees joined.  It
is appended to the defaults array at slot 3, so `defaults[i]` stays "the hash of an empty
subtree of height i".

That invariant is what makes the fold's right-edge case correct: hashing against
`defaults[level]` gives the same root as hashing against a genuinely empty subtree. -/
def A_block_3221258955042269759 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_extract_from_storage_value_dynamict_bytes32 "_5"
      (s₀["split_expr_3"]!!) (s₀["_4"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_fun_efficientHash "expr_1" (s₁["_5"]!!) (s₁["_5"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr 3
          (s₂["expr_1"]!!)) s₂ s₃ ∧
        s₉ = s₃⟦"size" ↦ 0⟧⟦"_6" ↦ 0⟧

lemma block_3221258955042269759_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3221258955042269759_concrete_of_code s₀ s₉ →
  Spec A_block_3221258955042269759 s₀ s₉ := by
  unfold block_3221258955042269759_concrete_of_code A_block_3221258955042269759
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma block_3221258955042269759_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3221258955042269759 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ :=
    extract_from_storage_value_dynamict_bytes32_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hs2 : isOk s₂ := fun_efficientHash_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ :=
    array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk h3nf
      (Spec_ok_unfold hs2 h3nf h₃)
  simpa [isOk_insert] using hs3

lemma block_3221258955042269759_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_3221258955042269759 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_3221258955042269759_isOk hok hnf h)

/-! ### Growing the tree, step two

Read the level's last node, hash it with itself to make the new default, and push that onto
the defaults array at slot 3.  So this block writes slot 3 and one keccak image, and
nothing else. -/

private lemma b3221_nf {s₉ : State} (hnf : ¬ ❓ s₉) {s₁ s₂ s₃ : State}
    (h₂ : Spec (A_fun_efficientHash "expr_1" (s₁["_5"]!!) (s₁["_5"]!!)) s₁ s₂)
    (h₃ : Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr 3
      (s₂["expr_1"]!!)) s₂ s₃)
    (heq : s₉ = s₃⟦"size" ↦ 0⟧⟦"_6" ↦ 0⟧) :
    ¬ ❓ s₃ ∧ ¬ ❓ s₂ ∧ ¬ ❓ s₁ := by
  subst heq
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  exact ⟨h3nf, h2nf, fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)⟩

/-- **KECCAK WINDOW.**  A pure extract, the default-node hash, and the push. -/
lemma block_3221258955042269759_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm 3 < 18446744073709551616)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_block_3221258955042269759 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  obtain ⟨h3nf, h2nf, h1nf⟩ := b3221_nf hnf h₂ h₃ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := extract_from_storage_value_dynamict_bytes32_isOk h1nf a₁
  have e1 : s₁.evm = s₀.evm := extract_from_storage_value_dynamict_bytes32_evm hok a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := fun_efficientHash_isOk hs1 a₂
  obtain ⟨hR2, hC2⟩ := fun_efficientHash_config hs1 (by rw [e1]; exact hR)
    (by rw [e1]; exact hC) a₂
  obtain ⟨hR3, hC3⟩ := array_push_config hs2 h3nf
    (by rw [fun_efficientHash_sload hs1 a₂, e1]; exact hfits) hR2 hC2
    (Spec_ok_unfold hs2 h3nf h₃)
  subst heq
  simpa only [evm_insert] using ⟨hR3, hC3⟩

/-- **CLEAN FLAG, BACKWARDS.**  Two hashes: the default node and the push's address. -/
lemma block_3221258955042269759_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm 3 < 18446744073709551616)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_3221258955042269759 s₀ s₉) : Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  obtain ⟨h3nf, h2nf, h1nf⟩ := b3221_nf hnf h₂ h₃ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := extract_from_storage_value_dynamict_bytes32_isOk h1nf a₁
  have e1 : s₁.evm = s₀.evm := extract_from_storage_value_dynamict_bytes32_evm hok a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := fun_efficientHash_isOk hs1 a₂
  rw [heq, evm_insert, evm_insert] at hclean
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    array_push_clean hs2 h3nf (by rw [fun_efficientHash_sload hs1 a₂, e1]; exact hfits)
      hclean (Spec_ok_unfold hs2 h3nf h₃)
  rw [← e1]
  exact fun_efficientHash_clean hs1 c2 a₂

/-- **STORAGE FRAME: SLOT 3 AND NOTHING ELSE.**

The defaults array's length lives at slot 3; the new default's element lands on a keccak
image.  Every other constant-numbered slot is untouched -- including slot 1, which is what
the leaf counter needs from the growth path. -/
lemma block_3221258955042269759_sload_of_ne {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm 3 < 18446744073709551616)
    (hc3 : c ≠ 3)
    (hclow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm 3).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_block_3221258955042269759 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  obtain ⟨h3nf, h2nf, h1nf⟩ := b3221_nf hnf h₂ h₃ heq
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := extract_from_storage_value_dynamict_bytes32_isOk h1nf a₁
  have e1 : s₁.evm = s₀.evm := extract_from_storage_value_dynamict_bytes32_evm hok a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := fun_efficientHash_isOk hs1 a₂
  have e2 : ∀ q, Clear.EVMState.sload s₂.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q; rw [fun_efficientHash_sload hs1 a₂, e1]
  obtain ⟨hR2, hC2⟩ := fun_efficientHash_config hs1 (by rw [e1]; exact hR)
    (by rw [e1]; exact hC) a₂
  rw [heq, evm_insert, evm_insert] at hclean ⊢
  rw [array_push_sload_frame_of_low_slot_of_clean hs2 h3nf (by rw [e2]; exact hfits)
      hc3 hclow (by rw [e2]; exact hidx) hR2 hC2 hclean (Spec_ok_unfold hs2 h3nf h₃), e2]

end

end L2InteropCommitmentTree.Common
