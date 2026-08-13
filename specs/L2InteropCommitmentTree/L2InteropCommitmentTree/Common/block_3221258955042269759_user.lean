import Clear.ReasoningPrinciple
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

end

end L2InteropCommitmentTree.Common
