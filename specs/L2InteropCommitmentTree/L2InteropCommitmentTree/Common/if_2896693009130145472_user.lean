import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2896693009130145472_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The pre-check overflow guard**: `if eq(value, not(0)) { panic_error_0x11() }`.

Note this checks BEFORE the addition -- it panics when the input is already the maximum
-- whereas `checked_add_uint256` adds first and compares afterwards.  Same condition,
opposite order. -/
def A_if_2896693009130145472 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec A_panic_error_0x11 s₀ s ∧
    (s₀["value"]!! = s₀["split_expr_0"]!! → s₉ = s) ∧
    (s₀["value"]!! ≠ s₀["split_expr_0"]!! → s₉ = s₀)

lemma if_2896693009130145472_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2896693009130145472_concrete_of_code s₀ s₉ →
  Spec A_if_2896693009130145472 s₀ s₉ := by
  unfold if_2896693009130145472_concrete_of_code A_if_2896693009130145472
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

lemma if_2896693009130145472_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2896693009130145472 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hp, h₁, h₂⟩ := h
  by_cases hg : s₀["value"]!! = s₀["split_expr_0"]!!
  · have hsnf : ¬ ❓ s := by rw [h₁ hg] at hnf; exact hnf
    rw [h₁ hg]
    exact panic_error_0x11_isOk hok (Spec_ok_unfold hok hsnf hp)
  · rw [h₂ hg]; exact hok

lemma if_2896693009130145472_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2896693009130145472 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_2896693009130145472_isOk hok hnf h)

/-- **OFF THE OVERFLOW PATH THE GUARD DOES NOTHING.**  It panics only when the value is
already `2^256 - 1`; anywhere else the state passes through.  This is the checked
increment's guard, so "the counter went up by one" needs exactly this. -/
lemma if_2896693009130145472_id_of_ne {s₀ s₉ : State}
    (hne : s₀["value"]!! ≠ s₀["split_expr_0"]!!)
    (h : A_if_2896693009130145472 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨_, _, _, hid⟩ := h
  exact hid hne

end

end L2InteropCommitmentTree.Common
