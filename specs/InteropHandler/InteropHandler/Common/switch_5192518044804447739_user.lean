import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.switch_5192518044804447739_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    switch lt(expr_3, _2) case 0 { expr_4 := _2 } default { expr_4 := expr_3 }

`lt` yields `1` when `expr_3 < _2` and `0` otherwise, so the `case 0` arm runs
exactly when `_2 ≤ expr_3` (assigning `_2`) and the `default` arm exactly when
`expr_3 < _2` (assigning `expr_3`).  Either way the value written is the SMALLER
of the two operands, and nothing else moves:

    expr_4 = min expr_3 _2,  EVM untouched, all other variables unchanged.

Genuine self-contained characterization: it does not mention
`switch_5192518044804447739_concrete_of_code`, so the bridge lemma below carries
real content instead of degenerating to `concrete → concrete`.
-/
def A_switch_5192518044804447739 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"expr_4" ↦ min (s₀["expr_3"]!!) (s₀["_2"]!!)⟧

lemma switch_5192518044804447739_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5192518044804447739_concrete_of_code s₀ s₉ →
  Spec A_switch_5192518044804447739 s₀ s₉ := by
  unfold switch_5192518044804447739_concrete_of_code A_switch_5192518044804447739
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  by_cases hlt : (Ok evm store)["expr_3"]!! < (Ok evm store)["_2"]!!
  · rw [min_eq_left (le_of_lt hlt)]
    rw [if_neg (by simp [hlt])] at hc
    exact hc.symm
  · rw [min_eq_right (le_of_not_lt hlt)]
    rw [if_pos (by simp [hlt])] at hc
    exact hc.symm

end

end InteropHandler.Common
