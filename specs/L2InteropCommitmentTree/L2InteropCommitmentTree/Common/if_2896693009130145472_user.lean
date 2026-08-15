import Clear.ReasoningPrinciple
import specs.KeccakLowSlot
import specs.KeccakClean

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

/-- **STORAGE FRAME.**  Neither branch writes storage: off the overflow path the guard is
the identity, and on it the panic writes memory and reverts -- which in this model sets a
flag and leaves `account_map` alone.  So this is UNCONDITIONAL, and a caller carrying a slot
across the checked increment needs no case analysis on whether the guard fired. -/
lemma if_2896693009130145472_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_if_2896693009130145472 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨sp, hsp, hfire, hid⟩ := h
  by_cases hg : s₀["value"]!! = s₀["split_expr_0"]!!
  · have hpnf : ¬ ❓ sp := by rw [hfire hg] at hnf; exact hnf
    rw [hfire hg]
    exact panic_error_0x11_sload hok (Spec_ok_unfold hok hpnf hsp)
  · rw [hid hg]

/-- **KECCAK WINDOW.**  Either branch: the overflow panic only writes memory. -/
lemma if_2896693009130145472_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_if_2896693009130145472 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s, hs, hpos, hneg⟩ := h
  by_cases hc : s₀["value"]!! = s₀["split_expr_0"]!!
  · rw [hpos hc]
    exact panic_error_0x11_config hok hR hC (Spec_ok_unfold hok (by rw [hpos hc] at hnf; exact hnf) hs)
  · rw [hneg hc]; exact ⟨hR, hC⟩

/-- **CLEAN FLAG.**  Neither branch hashes. -/
lemma if_2896693009130145472_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_2896693009130145472 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s, hs, hpos, hneg⟩ := h
  by_cases hc : s₀["value"]!! = s₀["split_expr_0"]!!
  · rw [hpos hc]
    exact panic_error_0x11_clean hok (Spec_ok_unfold hok (by rw [hpos hc] at hnf; exact hnf) hs)
  · rw [hneg hc]

end

end L2InteropCommitmentTree.Common
