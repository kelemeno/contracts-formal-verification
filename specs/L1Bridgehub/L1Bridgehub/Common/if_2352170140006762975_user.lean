import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L1Bridgehub.L1Bridgehub.Common.if_2352170140006762975_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Inline panic guard**, code 50 (0x32, array index out of bounds).

`if iszero(split_expr_4) { … revert }` -- so the panic fires when the flag is ZERO and the
state is left alone otherwise.  Reverts inline with Solidity's built-in `Panic(uint256)`
rather than calling `panic_error_*`, so this branch is the whole revert. -/
def A_if_2352170140006762975 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 1313373041 224
  let sm := Clear.State.multifill ["split_expr_5"] [sel] s₀
  let m1 := Clear.State.multifill ["split_expr_5"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_5"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 4 50⟧
  (s₀["split_expr_4"]!! = 0 → s₉ = m2🇪⟦Clear.EVMState.evm_revert m2.evm 0 36⟧) ∧
  (s₀["split_expr_4"]!! ≠ 0 → s₉ = s₀)

lemma if_2352170140006762975_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2352170140006762975_concrete_of_code s₀ s₉ →
  Spec A_if_2352170140006762975 s₀ s₉ := by
  unfold if_2352170140006762975_concrete_of_code A_if_2352170140006762975
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

lemma if_2352170140006762975_isOk {s₀ s₉ : State} (hok : isOk s₀) (h : A_if_2352170140006762975 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["split_expr_4"]!! = 0
    · rw [h₁ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
    · rw [h₂ hg]; simp [isOk]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_2352170140006762975_not_break {s₀ s₉ : State} (hok : isOk s₀) (h : A_if_2352170140006762975 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_2352170140006762975_isOk hok h)

end

end L1Bridgehub.Common
