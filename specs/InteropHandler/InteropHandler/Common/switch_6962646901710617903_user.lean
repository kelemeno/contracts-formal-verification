import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.switch_6962646901710617903_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    switch lt(var_start, expr) case 0 { expr_1 := expr } default { expr_1 := var_start }

`lt` yields `1` when `var_start < expr` and `0` otherwise, so `case 0` runs
exactly when `expr ≤ var_start` (assigning `expr`) and `default` exactly when
`var_start < expr` (assigning `var_start`).  Either way the value written is the
SMALLER operand — the companion clamp to `switch_6095062188052834118`, pinning a
slice's start below its (already clamped) end:

    expr_1 = min var_start expr,  EVM untouched, all other variables unchanged.

Genuine self-contained characterization: it does not mention
`switch_6962646901710617903_concrete_of_code`, so the bridge lemma carries real
content rather than degenerating to `concrete → concrete`.
-/
def A_switch_6962646901710617903 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"expr_1" ↦ min (s₀["var_start"]!!) (s₀["expr"]!!)⟧

lemma switch_6962646901710617903_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6962646901710617903_concrete_of_code s₀ s₉ →
  Spec A_switch_6962646901710617903 s₀ s₉ := by
  unfold switch_6962646901710617903_concrete_of_code A_switch_6962646901710617903
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  by_cases hlt : (Ok evm store)["var_start"]!! < (Ok evm store)["expr"]!!
  · rw [min_eq_left (le_of_lt hlt)]
    rw [if_neg (by simp [hlt])] at hc
    exact hc.symm
  · rw [min_eq_right (le_of_not_lt hlt)]
    rw [if_pos (by simp [hlt])] at hc
    exact hc.symm

end

end InteropHandler.Common
