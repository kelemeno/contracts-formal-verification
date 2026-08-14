import Clear.ReasoningPrinciple
import specs.StateOk
import specs.StorageFrame

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_7624433659449274775_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The increment's overflow guard**: `if gt(x, sum) { panic_error_0x11() }`.

Panic `0x11` is arithmetic overflow.  As with the other function-calling guards the
panic's `Spec` sits OUTSIDE the branch and the `if` selects between its result and
the untouched state. -/
def A_if_7624433659449274775 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec A_panic_error_0x11 s₀ s ∧
    (s₀["x"]!! ≤ s₀["sum"]!! → s₉ = s₀) ∧
    (¬ (s₀["x"]!! ≤ s₀["sum"]!!) → s₉ = s)

lemma if_7624433659449274775_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7624433659449274775_concrete_of_code s₀ s₉ →
  Spec A_if_7624433659449274775 s₀ s₉ := by
  unfold if_7624433659449274775_concrete_of_code A_if_7624433659449274775
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

lemma if_7624433659449274775_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_7624433659449274775 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hp, h₁, h₂⟩ := h
  by_cases hg : s₀["x"]!! ≤ s₀["sum"]!!
  · rw [h₁ hg]; exact hok
  · have hsnf : ¬ ❓ s := by rw [h₂ hg] at hnf; exact hnf
    rw [h₂ hg]
    exact panic_error_0x11_isOk hok (Spec_ok_unfold hok hsnf hp)

lemma if_7624433659449274775_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_7624433659449274775 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_7624433659449274775_isOk hok hnf h)


/-- **STORAGE FRAME.**  Overflow guard: either it passes and the state is unchanged, or it
panics -- and a panic writes no storage either. -/
lemma if_7624433659449274775_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_if_7624433659449274775 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s, hs, hpos, hneg⟩ := h
  by_cases hc : s₀["x"]!! ≤ s₀["sum"]!!
  · rw [hpos hc]
  · have hse : s₉ = s := hneg hc
    subst hse
    exact panic_error_0x11_sload hok (Spec_ok_unfold hok hnf hs)

end

end L2InteropCommitmentTree.Common
