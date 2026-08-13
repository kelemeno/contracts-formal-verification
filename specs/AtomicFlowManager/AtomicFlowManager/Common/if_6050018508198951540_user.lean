import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6050018508198951540_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The sortedness revert: `ManagerBundleHashesNotSorted()`.**

```
    if iszero(split_expr_1) {
      let split_expr_2 := shl(225, 2012753307)
      mstore(0, split_expr_2)
      revert(0, 4)
    }
```

`shl(225, 2012753307)` is the 4-byte custom-error selector `0xeff05b36`, which is
`keccak("ManagerBundleHashesNotSorted()")[0:4]` — confirmed against every `error`
declaration in era-contracts, and the only match among 538.  So this is the guard
the ascending-order comparison feeds: `split_expr_1` is the flag computed by
block_4720374723594237178 / block_253019513998627002, and a zero flag (previous
entry NOT below current) reverts the whole call with that named error.

That is the concrete end of `AttackVectors/FlowCanonical.lean`: the abstract file
proves what neighbour-only sortedness buys globally, and this is the deployed
check that enforces it, named. -/
def A_if_6050018508198951540 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 2012753307 225
  let sm := Clear.State.multifill ["split_expr_2"] [sel] s₀
  let sr := Clear.State.multifill ["split_expr_2"] [sel]
      s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_2"]!!)⟧
  (s₀["split_expr_1"]!! = 0 → s₉ = sr🇪⟦Clear.EVMState.evm_revert sr.evm 0 4⟧) ∧
  (s₀["split_expr_1"]!! ≠ 0 → s₉ = s₀)

lemma if_6050018508198951540_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6050018508198951540_concrete_of_code s₀ s₉ →
  Spec A_if_6050018508198951540 s₀ s₉ := by
  unfold if_6050018508198951540_concrete_of_code A_if_6050018508198951540
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  dsimp only at hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

/-- Output is `Ok` on both branches: the revert branch is `mstore` + `revert`, and a
revert is an `Ok` state carrying the flag. -/
lemma if_6050018508198951540_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_6050018508198951540 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["split_expr_1"]!! = 0
    · -- outer `setEvm` strips by simp; the multifill needs its own `isOk` argument
      rw [h₁ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
    · rw [h₂ hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_6050018508198951540_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_6050018508198951540 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_6050018508198951540_isOk hok h)

end

end AtomicFlowManager.Common
