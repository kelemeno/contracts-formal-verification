import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.if_9006375582650777893_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The replay guard**: `if iszero(condition) { revert WithdrawalAlreadyFinalized() }`.

The 4-byte payload is `shl(226, 732062997) = 0xae899454`, which resolves against
era-contracts to `WithdrawalAlreadyFinalized()` -- so this is the check that stops a
withdrawal being finalized twice, and it reverts with a named error rather than a bare
panic.

Note the shift is 226, not the usual 224: solc shifts by `224 + k` when the selector's
low `k` bits are zero, so a bare `shl(224, …)` assumption would mis-read this one. -/
def A_if_9006375582650777893 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 732062997 226
  let sm := Clear.State.multifill ["split_expr_0"] [sel] s₀
  let m := Clear.State.multifill ["split_expr_0"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_0"]!!)⟧
  (s₀["condition"]!! = 0 → s₉ = m🇪⟦Clear.EVMState.evm_revert m.evm 0 4⟧) ∧
  (s₀["condition"]!! ≠ 0 → s₉ = s₀)

lemma if_9006375582650777893_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9006375582650777893_concrete_of_code s₀ s₉ →
  Spec A_if_9006375582650777893 s₀ s₉ := by
  unfold if_9006375582650777893_concrete_of_code A_if_9006375582650777893
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  dsimp only at hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

/-- Output is `Ok` on both branches: a revert carries the flag rather than changing the
constructor. -/
lemma if_9006375582650777893_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_9006375582650777893 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["condition"]!! = 0
    · rw [h₁ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
    · rw [h₂ hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_9006375582650777893_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_9006375582650777893 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_9006375582650777893_isOk hok h)

end

end L1Nullifier.Common
