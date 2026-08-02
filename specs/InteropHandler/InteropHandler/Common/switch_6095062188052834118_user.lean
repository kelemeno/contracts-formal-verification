import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.switch_6095062188052834118_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    switch lt(var_end, _1) case 0 { expr := _1 } default { expr := var_end }

`lt` yields `1` when `var_end < _1` and `0` otherwise, so `case 0` runs exactly
when `_1 ≤ var_end` (assigning `_1`) and `default` exactly when `var_end < _1`
(assigning `var_end`).  Either way the value written is the SMALLER operand —
this is the standard `min(end, length)` clamp of a slice bound:

    expr = min var_end _1,  EVM untouched, all other variables unchanged.

Genuine self-contained characterization: it does not mention
`switch_6095062188052834118_concrete_of_code`, so the bridge lemma carries real
content rather than degenerating to `concrete → concrete`.
-/
def A_switch_6095062188052834118 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"expr" ↦ min (s₀["var_end"]!!) (s₀["_1"]!!)⟧

lemma switch_6095062188052834118_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_6095062188052834118_concrete_of_code s₀ s₉ →
  Spec A_switch_6095062188052834118 s₀ s₉ := by
  unfold switch_6095062188052834118_concrete_of_code A_switch_6095062188052834118
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  by_cases hlt : (Ok evm store)["var_end"]!! < (Ok evm store)["_1"]!!
  · rw [min_eq_left (le_of_lt hlt)]
    rw [if_neg (by simp [hlt])] at hc
    exact hc.symm
  · rw [min_eq_right (le_of_not_lt hlt)]
    rw [if_pos (by simp [hlt])] at hc
    exact hc.symm

end

end InteropHandler.Common
