import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7113846640530982357_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The SUBTRACTION-UNDERFLOW guard, as a dichotomy:

    if gt(diff_1, var_i) { panic_error_0x11() }

`diff_1` is `sub(var_i, var_left)`, so `diff_1 > var_i` can only happen if that
subtraction wrapped — i.e. `var_left > var_i`. Panic 0x11 is Solidity's arithmetic
overflow/underflow panic, which is what this encodes at the Yul level.

Note the sense: the SAFE branch is `diff_1 ≤ var_i`, and it leaves the state untouched. -/
def A_if_7113846640530982357 (s₀ s₉ : State) : Prop :=
  (s₀["diff_1"]!! ≤ s₀["var_i"]!! → s₉ = s₀) ∧
  (¬ (s₀["diff_1"]!! ≤ s₀["var_i"]!!) → ∃ s, Spec A_panic_error_0x11 s₀ s ∧ s₉ = s)

lemma if_7113846640530982357_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7113846640530982357_concrete_of_code s₀ s₉ →
  Spec A_if_7113846640530982357 s₀ s₉ := by
  unfold if_7113846640530982357_concrete_of_code A_if_7113846640530982357
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hp, heq⟩ := hc
  constructor
  · intro hle
    rw [if_pos hle] at heq
    exact heq.symm
  · intro hgt
    rw [if_neg hgt] at heq
    exact ⟨s, hp, heq.symm⟩
/-- **THE GUARD'S OUTPUT IS `Ok`.**  Either the state is untouched (no underflow), or it is
`panic_error_0x11`'s output — and a revert yields an `Ok` state carrying the reverted flag.

`¬ ❓ s₉` is required: `Spec` is vacuous on an out-of-fuel result, so without it the panic
branch could hand back `OutOfFuel`. -/
lemma if_7113846640530982357_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_7113846640530982357 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨hle, hgt⟩ := h
    by_cases hg : (Ok evm store)["diff_1"]!! ≤ (Ok evm store)["var_i"]!!
    · rw [hle hg]; simp [isOk]
    · obtain ⟨s, hp, rfl⟩ := hgt hg
      exact panic_error_0x11_isOk (by simp [isOk])
        (Spec_ok_unfold (P := A_panic_error_0x11) (by simp [isOk]) hnf hp)
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_7113846640530982357_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_7113846640530982357 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_7113846640530982357_isOk hok hnf h)

end

end AtomicFlowManager.Common
