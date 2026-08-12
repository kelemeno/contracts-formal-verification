import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2600721580863995212_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The array-bounds guard, as a DICHOTOMY on the flag rather than an alias to its
concrete spec:

    if iszero(split_expr_1) { panic_error_0x32() }

`split_expr_1` is `lt(index, length)`, so a ZERO flag means the index is out of bounds
and control goes to `panic_error_0x32`; a nonzero flag leaves the state untouched.

Stating it this way is what lets callers conclude anything about the guard's output —
with the alias form they get an opaque blob, which is why the loops composing through
this could not close their `ABreak`. -/
def A_if_2600721580863995212 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_1"]!! ≠ 0 → s₉ = s₀) ∧
  (s₀["split_expr_1"]!! = 0 → ∃ s, Spec A_panic_error_0x32 s₀ s ∧ s₉ = s)

lemma if_2600721580863995212_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2600721580863995212_concrete_of_code s₀ s₉ →
  Spec A_if_2600721580863995212 s₀ s₉ := by
  unfold if_2600721580863995212_concrete_of_code A_if_2600721580863995212
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hp, heq⟩ := hc
  constructor
  · intro hne
    rw [if_neg hne] at heq
    exact heq.symm
  · intro hz
    rw [if_pos hz] at heq
    exact ⟨s, hp, heq.symm⟩
/-- **THE GUARD'S OUTPUT IS `Ok`.**  Either the state is untouched, or it is the panic's
output — and a revert yields an `Ok` state carrying the reverted flag.

`¬ ❓ s₉` is REQUIRED, not decoration: `Spec` is vacuous on an out-of-fuel result, so
without it the panic branch could hand back `OutOfFuel` and the conclusion would be false.
Callers have this hypothesis wherever they need the lemma. -/
lemma if_2600721580863995212_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2600721580863995212 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨hne, hz⟩ := h
    by_cases hg : (Ok evm store)["split_expr_1"]!! = 0
    · obtain ⟨s, hp, rfl⟩ := hz hg
      exact panic_error_0x32_isOk (by simp [isOk])
        (Spec_ok_unfold (P := A_panic_error_0x32) (s := Ok evm store) (by simp [isOk]) hnf hp)
    · rw [hne hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_2600721580863995212_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2600721580863995212 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_2600721580863995212_isOk hok hnf h)

end

end AtomicFlowManager.Common
