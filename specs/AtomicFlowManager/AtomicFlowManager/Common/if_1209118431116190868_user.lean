import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1209118431116190868_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- A **plain revert guard**: `if iszero(split_expr_4) { revert(0, 0) }`.

Unlike the panic guards in this directory this one reverts INLINE rather than
calling `panic_error_*`, so there is no nested `Spec` to delegate to — the whole
behaviour is the branch itself.  Note the polarity: the state is left alone when
`split_expr_4` is NONZERO. -/
def A_if_1209118431116190868 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_4"]!! = 0 → s₉ = s₀🇪⟦Clear.EVMState.evm_revert s₀.evm 0 0⟧) ∧
  (s₀["split_expr_4"]!! ≠ 0 → s₉ = s₀)

lemma if_1209118431116190868_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1209118431116190868_concrete_of_code s₀ s₉ →
  Spec A_if_1209118431116190868 s₀ s₉ := by
  unfold if_1209118431116190868_concrete_of_code A_if_1209118431116190868
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  -- `hc` arrives still wrapped in the `Spec` coercion: defeq to the branch equation
  -- but not syntactically it, so `rw [if_pos]` misses it.  Casting
  -- through the expected type forces the reduction.
  replace hc : (if (Ok evm store)["split_expr_4"]!! = 0
      then (Ok evm store)🇪⟦Clear.EVMState.evm_revert (Ok evm store).evm 0 0⟧
      else (Ok evm store)) = s₉ := hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

/-- **The guard's output is `Ok` on BOTH branches.**  A revert in this model is an
`Ok` state carrying the reverted flag, not a separate constructor, so an inline
`revert(0,0)` preserves `isOk` — which is why this lemma needs no `¬ ❓ s₉`
hypothesis, unlike the panic guards that delegate through a nested `Spec`. -/
lemma if_1209118431116190868_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_1209118431116190868 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["split_expr_4"]!! = 0
    · rw [h₁ hg]; simp [isOk, State.setEvm]
    · rw [h₂ hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_1209118431116190868_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_1209118431116190868 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_1209118431116190868_isOk hok h)

end

end AtomicFlowManager.Common
