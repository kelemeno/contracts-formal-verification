import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4590714779410500988_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The array-length guard**: `if iszero(lt(oldLen, 2^64)) { panic_error_0x41() }`.

Panic `0x41` is "allocated too much memory or array too large".  So a storage array
cannot grow past `2^64 - 1` entries — the bound the IMT's node array lives under.

Note the emitted shape: the panic's `Spec` sits OUTSIDE the branch, with the `if`
choosing between its result and the untouched state, rather than the call being
nested inside the taken branch. -/
def A_if_4590714779410500988 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec A_panic_error_0x41 s₀ s ∧
    (s₀["split_expr_0"]!! = 0 → s₉ = s) ∧
    (s₀["split_expr_0"]!! ≠ 0 → s₉ = s₀)

lemma if_4590714779410500988_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4590714779410500988_concrete_of_code s₀ s₉ →
  Spec A_if_4590714779410500988 s₀ s₉ := by
  unfold if_4590714779410500988_concrete_of_code A_if_4590714779410500988
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

/-- Output is `Ok` on both branches: the panic's output is `Ok` (a revert carries a
flag rather than leaving the constructor), and the other branch is the input. -/
lemma if_4590714779410500988_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_4590714779410500988 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hp, h₁, h₂⟩ := h
  by_cases hg : s₀["split_expr_0"]!! = 0
  · have hsnf : ¬ ❓ s := by rw [h₁ hg] at hnf; exact hnf
    rw [h₁ hg]
    exact panic_error_0x41_isOk hok (Spec_ok_unfold hok hsnf hp)
  · rw [h₂ hg]; exact hok

lemma if_4590714779410500988_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_4590714779410500988 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_4590714779410500988_isOk hok hnf h)


/-- **THE LENGTH FITS: the guard changes nothing.**

`array.push` panics (0x41) only if the array is already `2 ^ 64` long.  Off that path the
guard is the identity, which is what a proof that the push INCREMENTS the length needs --
otherwise the length fact would have to be threaded through a reverting state.

A real tree never reaches `2 ^ 64` levels-worth of nodes, but that is an argument about
reachability, not something this lemma assumes: the hypothesis is simply the flag. -/
lemma if_4590714779410500988_id_of_ne {s₀ s₉ : State}
    (hne : s₀["split_expr_0"]!! ≠ 0)
    (h : A_if_4590714779410500988 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨_, _, _, hneg⟩ := h
  exact hneg hne

end

end L2InteropCommitmentTree.Common
