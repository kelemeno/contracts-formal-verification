import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2726844535930192361_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The skip guard**: `if iszero(split_expr_9) { continue }`.

Unlike every other guard in this directory this one does not revert — it CONTINUES,
so its output is a `Continue` checkpoint rather than an `Ok` state.  In the leg loop
that means "this leg is not in the state we are looking for, move to the next one",
which is why the loop can process a subset of legs without failing.

Consequence for the plumbing: there is no `isOk` lemma here, and there cannot be.
What downstream needs is `not_break` — a `Continue` is not a `Break`, so the
enclosing loop's `ABreak` obligation still closes. -/
def A_if_2726844535930192361 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_9"]!! = 0 → s₉ = 🔁s₀) ∧
  (s₀["split_expr_9"]!! ≠ 0 → s₉ = s₀)

lemma if_2726844535930192361_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2726844535930192361_concrete_of_code s₀ s₉ →
  Spec A_if_2726844535930192361 s₀ s₉ := by
  unfold if_2726844535930192361_concrete_of_code A_if_2726844535930192361
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

/-- **Neither branch breaks.**  The skip branch is a `Continue` checkpoint and the
other leaves the state alone, so the enclosing loop never sees a `Break` from here. -/
lemma if_2726844535930192361_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_2726844535930192361 s₀ s₉) : ¬ isBreak s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["split_expr_9"]!! = 0
    · rw [h₁ hg]; simp [State.isBreak, State.setContinue]
    · rw [h₂ hg]; simp [State.isBreak]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

/-- The output is `Ok` exactly on the non-skip branch — the form the enclosing block
needs, since `isOk` is unavailable in general here. -/
lemma if_2726844535930192361_isOk_of_ne {s₀ s₉ : State} (hok : isOk s₀)
    (hg : s₀["split_expr_9"]!! ≠ 0)
    (h : A_if_2726844535930192361 s₀ s₉) : isOk s₉ := by
  rw [h.2 hg]; exact hok

end

end AtomicFlowManager.Common
