import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.switch_8523945878344766818_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    switch lt(5, expr_4) case 0 { expr_5 := expr_4 } default { expr_5 := 5 }

Here the first `lt` operand is the LITERAL `5`.  `lt(5, expr_4)` yields `1` when
`5 < expr_4` and `0` otherwise, so `case 0` runs exactly when `expr_4 ≤ 5`
(assigning `expr_4`) and `default` exactly when `5 < expr_4` (assigning `5`).
Either way the value written is the SMALLER of the two — a cap of `expr_4` at the
constant `5`:

    expr_5 = min 5 expr_4,  EVM untouched, all other variables unchanged.

Genuine self-contained characterization: it does not mention
`switch_8523945878344766818_concrete_of_code`, so the bridge lemma carries real
content rather than degenerating to `concrete → concrete`.
-/
def A_switch_8523945878344766818 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"expr_5" ↦ min (5 : UInt256) (s₀["expr_4"]!!)⟧

lemma switch_8523945878344766818_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8523945878344766818_concrete_of_code s₀ s₉ →
  Spec A_switch_8523945878344766818 s₀ s₉ := by
  unfold switch_8523945878344766818_concrete_of_code A_switch_8523945878344766818
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  by_cases hlt : (5 : UInt256) < (Ok evm store)["expr_4"]!!
  · rw [min_eq_left (le_of_lt hlt)]
    rw [if_neg (by simp [hlt])] at hc
    exact hc.symm
  · rw [min_eq_right (le_of_not_lt hlt)]
    rw [if_pos (by simp [hlt])] at hc
    exact hc.symm

end

end InteropHandler.Common
