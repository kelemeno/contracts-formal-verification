import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6945705467323769142_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The calldata array-bounds guard, as a DICHOTOMY on the flag (cf. `if_2600721580863995212`,
the memory-array counterpart):

    if iszero(split_expr_0) { panic_error_0x32() }

`split_expr_0` is `lt(index, length)`, so a ZERO flag is an out-of-bounds index. -/
def A_if_6945705467323769142 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_0"]!! ≠ 0 → s₉ = s₀) ∧
  (s₀["split_expr_0"]!! = 0 → ∃ s, Spec A_panic_error_0x32 s₀ s ∧ s₉ = s)

lemma if_6945705467323769142_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6945705467323769142_concrete_of_code s₀ s₉ →
  Spec A_if_6945705467323769142 s₀ s₉ := by
  unfold if_6945705467323769142_concrete_of_code A_if_6945705467323769142
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
lemma if_6945705467323769142_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_6945705467323769142 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨hne, hz⟩ := h
    by_cases hg : (Ok evm store)["split_expr_0"]!! = 0
    · obtain ⟨s, hp, rfl⟩ := hz hg
      exact panic_error_0x32_isOk (by simp [isOk])
        (Spec_ok_unfold (P := A_panic_error_0x32) (s := Ok evm store) (by simp [isOk]) hnf hp)
    · rw [hne hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_6945705467323769142_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_6945705467323769142 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_6945705467323769142_isOk hok hnf h)

end

end AtomicFlowManager.Common
