import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_294889826768454570_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Halve both node counts** — one level up the tree:

```
    var_maxNodeNumber    := checked_div_uint256(var_maxNodeNumber)
    var_oldMaxNodeNumber := checked_div_uint256(var_oldMaxNodeNumber)
```

Both counts are divided by 2 in the same iteration, which is what keeps the loop's
second break condition (`oldMax == max`) meaningful: the two shrink in lockstep, so
they meet exactly when the old tree's levels run out. -/
def A_block_294889826768454570 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_checked_div_uint256 "var_maxNodeNumber" (s₀["var_maxNodeNumber"]!!)) s₀ s₁ ∧
    ∃ s₂, Spec (A_checked_div_uint256 "var_oldMaxNodeNumber" (s₁["var_oldMaxNodeNumber"]!!)) s₁ s₂ ∧
      s₉ = s₂

lemma block_294889826768454570_abs_of_concrete {s₀ s₉ : State} :
  Spec block_294889826768454570_concrete_of_code s₀ s₉ →
  Spec A_block_294889826768454570 s₀ s₉ := by
  unfold block_294889826768454570_concrete_of_code A_block_294889826768454570
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

/-- Output is `Ok`: two function returns in sequence. -/
lemma block_294889826768454570_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_294889826768454570 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  rw [heq] at hnf ⊢
  have h1nf : ¬ ❓ s₁ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok (Spec_ok_unfold hok h1nf h₁)
  exact checked_div_uint256_isOk hs1 (Spec_ok_unfold hs1 hnf h₂)

lemma block_294889826768454570_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_294889826768454570 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_294889826768454570_isOk hok hnf h)

/-- **THE EVM IS THE CALLER'S.**  Halving the two node counts is arithmetic on variables. -/
lemma block_294889826768454570_evm {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_294889826768454570 s₀ s₉) : s₉.evm = s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  rw [heq] at hnf ⊢
  have h1nf : ¬ ❓ s₁ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have a₁ := Spec_ok_unfold hok h1nf h₁
  have hs1 : isOk s₁ := checked_div_uint256_isOk hok a₁
  rw [checked_div_uint256_evm hs1 (Spec_ok_unfold hs1 hnf h₂),
    checked_div_uint256_evm hok a₁]

end

end L2InteropCommitmentTree.Common
