import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L1Bridgehub.L1Bridgehub.Common.if_4888609276936831298_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The chain-limit guard**: reverts with `ZKChainLimitReached()`.

Selector `shl(225, 806204481) = 0x601b6882`, resolved against era-contracts.  Fires when
`expr` is nonzero, and reverts inline with the bare 4-byte selector -- no diagnostic
payload, unlike `ManagerLegNotRevertable`.

Third distinct shift seen in this session: 224, 225 and 226 all occur, because solc uses
`224 + k` when the selector's low k bits are zero. -/
def A_if_4888609276936831298 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 806204481 225
  let sm := Clear.State.multifill ["split_expr_6"] [sel] s₀
  let m := Clear.State.multifill ["split_expr_6"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_6"]!!)⟧
  (s₀["expr"]!! = 0 → s₉ = s₀) ∧
  (s₀["expr"]!! ≠ 0 → s₉ = m🇪⟦Clear.EVMState.evm_revert m.evm 0 4⟧)

lemma if_4888609276936831298_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4888609276936831298_concrete_of_code s₀ s₉ →
  Spec A_if_4888609276936831298 s₀ s₉ := by
  unfold if_4888609276936831298_concrete_of_code A_if_4888609276936831298
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

lemma if_4888609276936831298_isOk {s₀ s₉ : State} (hok : isOk s₀) (h : A_if_4888609276936831298 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["expr"]!! = 0
    · rw [h₁ hg]; simp [isOk]
    · rw [h₂ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_4888609276936831298_not_break {s₀ s₉ : State} (hok : isOk s₀) (h : A_if_4888609276936831298 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_4888609276936831298_isOk hok h)

end

end L1Bridgehub.Common
