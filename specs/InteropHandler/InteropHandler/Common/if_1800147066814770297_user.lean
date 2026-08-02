import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_1800147066814770297_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    if iszero(expr_4) { expr_4 := eq(expr_3, 20) }

Yul's `if` fires on a nonzero guard and `iszero(v)` is nonzero exactly when
`v = 0`, so when `expr_4` is zero it is overwritten with the equality flag of
`expr_3` against `20` (`1` if equal, `0` otherwise); otherwise nothing moves.

Self-contained: does not mention `if_1800147066814770297_concrete_of_code`.
-/
def A_if_1800147066814770297 (s₀ s₉ : State) : Prop :=
  ((s₀["expr_4"]!!) = 0 →
      s₉ = s₀⟦"expr_4" ↦ (if (s₀["expr_3"]!!) = (20 : UInt256) then (1 : UInt256) else 0)⟧)
  ∧ ((s₀["expr_4"]!!) ≠ 0 → s₉ = s₀)

lemma if_1800147066814770297_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1800147066814770297_concrete_of_code s₀ s₉ →
  Spec A_if_1800147066814770297 s₀ s₉ := by
  unfold if_1800147066814770297_concrete_of_code A_if_1800147066814770297
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨?_, ?_⟩
  · intro hz
    rw [if_pos hz] at hc
    exact hc.symm
  · intro hnz
    rw [if_neg hnz] at hc
    exact hc.symm

end

end InteropHandler.Common
