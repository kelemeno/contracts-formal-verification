import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_6787653505677561102_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Grow the tree by one level, part 1: bump the level count and read the top default.**

```
    expr := fun_uncheckedInc(_2)            -- levels + 1, UNCHECKED
    sstore(0, expr)                         -- store the new level count
    split_expr_2 := checked_sub_uint256(expr)   -- (levels + 1) - 1, CHECKED
    _3, _4 := storage_array_index_access(3, split_expr_2)  -- defaults[levels]
    split_expr_3 := sload(_3)
```

The level count is written BEFORE the new level's node exists, and the default read is
at the OLD top index (`(levels+1) - 1 = levels`), so this reads the default that was
previously the topmost -- the input to the new one computed in part 2. -/
def A_block_6787653505677561102 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec (A_fun_uncheckedInc "expr" (s₀["_2"]!!)) s₀ s₁ ∧
    (let st := s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧
     ∃ s₂, Spec (A_checked_sub_uint256 "split_expr_2" (st["expr"]!!)) st s₂ ∧
       ∃ s₃, Spec (A_storage_array_index_access_bytes32_dyn__dyn "_3" "_4" 3
           (s₂["split_expr_2"]!!)) s₂ s₃ ∧
         s₉ = s₃⟦"split_expr_3" ↦ Clear.EVMState.sload s₃.evm (s₃["_3"]!!)⟧)

lemma block_6787653505677561102_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6787653505677561102_concrete_of_code s₀ s₉ →
  Spec A_block_6787653505677561102 s₀ s₉ := by
  unfold block_6787653505677561102_concrete_of_code A_block_6787653505677561102
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma block_6787653505677561102_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_6787653505677561102 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    exact h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_setEvm'] using hoo))
  have hs1 : isOk s₁ := fun_uncheckedInc_isOk h1nf (Spec_ok_unfold hok h1nf h₁)
  have hstok : isOk (s₁🇪⟦Clear.EVMState.sstore s₁.evm 0 (s₁["expr"]!!)⟧) := by
    simpa only [isOk_setEvm] using hs1
  have hs2 : isOk s₂ := checked_sub_uint256_isOk hstok h2nf (Spec_ok_unfold hstok h2nf h₂)
  have hs3 : isOk s₃ :=
    storage_array_index_access_bytes32_dyn__dyn_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  simpa [isOk_insert] using hs3

lemma block_6787653505677561102_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_6787653505677561102 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_6787653505677561102_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
