import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6747681429752853338_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- A **length bound guard**: `if gt(length, 0xffffffffffffffff) { revert(0, 0) }`.

`0xffffffffffffffff = 2^64 - 1` is solc's ceiling on an array length, so this is
the compiler rejecting a calldata/memory length that could not have been produced
honestly.  Reverts INLINE, so there is no nested `Spec`; the guard's whole content
is the branch.  Polarity: the state survives when the length is WITHIN the bound. -/
def A_if_6747681429752853338 (s₀ s₉ : State) : Prop :=
  (s₀["length"]!! ≤ 18446744073709551615 → s₉ = s₀) ∧
  (¬ (s₀["length"]!! ≤ 18446744073709551615) → s₉ = s₀🇪⟦Clear.EVMState.evm_revert s₀.evm 0 0⟧)

lemma if_6747681429752853338_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6747681429752853338_concrete_of_code s₀ s₉ →
  Spec A_if_6747681429752853338 s₀ s₉ := by
  unfold if_6747681429752853338_concrete_of_code A_if_6747681429752853338
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  -- `hc` arrives still wrapped in the `Spec` coercion: defeq to the branch equation
  -- but not syntactically it, so `rw [if_pos]` misses it.  Casting
  -- through the expected type forces the reduction.
  replace hc : (if (Ok evm store)["length"]!! ≤ 18446744073709551615
      then (Ok evm store)
      else (Ok evm store)🇪⟦Clear.EVMState.evm_revert (Ok evm store).evm 0 0⟧) = s₉ := hc
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
lemma if_6747681429752853338_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_6747681429752853338 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["length"]!! ≤ 18446744073709551615
    · rw [h₁ hg]; simp [isOk]
    · rw [h₂ hg]; simp [isOk, State.setEvm]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_6747681429752853338_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_6747681429752853338 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_6747681429752853338_isOk hok h)

end

end AtomicFlowManager.Common
