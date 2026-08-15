import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_5792510925045852942_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

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

/-- **STORAGE FRAME.**  The allocation-overflow check either passes or panics, and the
panic writes only memory. -/
lemma if_5792510925045852942_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_if_5792510925045852942 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s, hs, hpos, hneg⟩ := h
  by_cases hc : Fin.lor (s₀["split_expr_3"]!!) (s₀["split_expr_4"]!!) = 0
  · rw [hpos hc]
  · rw [hneg hc]
    exact panic_error_0x41_sload hok (Spec_ok_unfold hok (by rw [hneg hc] at hnf; exact hnf) hs)

/-- **KECCAK WINDOW.** -/
lemma if_5792510925045852942_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_if_5792510925045852942 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s, hs, hpos, hneg⟩ := h
  by_cases hc : Fin.lor (s₀["split_expr_3"]!!) (s₀["split_expr_4"]!!) = 0
  · rw [hpos hc]; exact ⟨hR, hC⟩
  · rw [hneg hc]
    exact panic_error_0x41_config hok hR hC
      (Spec_ok_unfold hok (by rw [hneg hc] at hnf; exact hnf) hs)

/-- **CLEAN FLAG.**  Neither branch hashes. -/
lemma if_5792510925045852942_clean {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_5792510925045852942 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s, hs, hpos, hneg⟩ := h
  by_cases hc : Fin.lor (s₀["split_expr_3"]!!) (s₀["split_expr_4"]!!) = 0
  · rw [hpos hc]
  · rw [hneg hc]
    exact panic_error_0x41_clean hok (Spec_ok_unfold hok (by rw [hneg hc] at hnf; exact hnf) hs)

end

end L2InteropCommitmentTree.Common
