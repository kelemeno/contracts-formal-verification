import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5792510925045852942_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- **The allocation-size guard**: `if or(split_expr_3, split_expr_4) { panic_error_0x41() }`.

Panics `0x41` ("allocated too much memory or array too large") when EITHER flag is set --
the two are separate overflow tests on an allocation size, combined with `or` so one
branch covers both. -/
def A_if_5792510925045852942 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec A_panic_error_0x41 s₀ s ∧
    (Fin.lor (s₀["split_expr_3"]!!) (s₀["split_expr_4"]!!) = 0 → s₉ = s₀) ∧
    (Fin.lor (s₀["split_expr_3"]!!) (s₀["split_expr_4"]!!) ≠ 0 → s₉ = s)

lemma if_5792510925045852942_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5792510925045852942_concrete_of_code s₀ s₉ →
  Spec A_if_5792510925045852942 s₀ s₉ := by
  unfold if_5792510925045852942_concrete_of_code A_if_5792510925045852942
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hp, heq⟩ := hc
  refine ⟨s, hp, ?_, ?_⟩
  · intro hg
    rw [if_pos hg] at heq
    exact heq.symm
  · intro hg
    rw [if_neg hg] at heq
    exact heq.symm

lemma if_5792510925045852942_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_5792510925045852942 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hp, h₁, h₂⟩ := h
  by_cases hg : Fin.lor (s₀["split_expr_3"]!!) (s₀["split_expr_4"]!!) = 0
  · rw [h₁ hg]; exact hok
  · have hsnf : ¬ ❓ s := by rw [h₂ hg] at hnf; exact hnf
    rw [h₂ hg]
    exact panic_error_0x41_isOk hok (Spec_ok_unfold hok hsnf hp)

lemma if_5792510925045852942_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_5792510925045852942 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_5792510925045852942_isOk hok hnf h)

end

end AtomicFlowManager.Common
