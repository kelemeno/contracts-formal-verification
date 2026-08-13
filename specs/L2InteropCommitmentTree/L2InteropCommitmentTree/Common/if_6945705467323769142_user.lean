import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6945705467323769142_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The empty-level guard**: `if iszero(split_expr_3) { panic_error_0x32() }`.

`split_expr_3` is the slot of the top LEVEL's array, read out of the array-of-arrays at
slot 2.  Zero there means that level holds no nodes, so panic `0x32` (array index out of
bounds) fires rather than the root being read from an empty array. -/
def A_if_6945705467323769142 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec A_panic_error_0x32 s₀ s ∧
    (s₀["split_expr_0"]!! = 0 → s₉ = s) ∧
    (s₀["split_expr_0"]!! ≠ 0 → s₉ = s₀)

lemma if_6945705467323769142_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6945705467323769142_concrete_of_code s₀ s₉ →
  Spec A_if_6945705467323769142 s₀ s₉ := by
  unfold if_6945705467323769142_concrete_of_code A_if_6945705467323769142
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

lemma if_6945705467323769142_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_6945705467323769142 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hp, h₁, h₂⟩ := h
  by_cases hg : s₀["split_expr_0"]!! = 0
  · have hsnf : ¬ ❓ s := by rw [h₁ hg] at hnf; exact hnf
    rw [h₁ hg]
    exact panic_error_0x32_isOk hok (Spec_ok_unfold hok hsnf hp)
  · rw [h₂ hg]; exact hok

lemma if_6945705467323769142_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_6945705467323769142 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_6945705467323769142_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common
