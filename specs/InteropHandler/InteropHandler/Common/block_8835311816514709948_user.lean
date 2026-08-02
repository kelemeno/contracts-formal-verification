import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_8835311816514709948_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_6 := and(split_expr_4, split_expr_5)
      let split_expr_7 := add(pos, split_expr_6)
      end_clear_sanitised_hrafn := add(split_expr_7, 32) }

Masks a length, adds it to the cursor `pos`, then advances one further word —
the standard "end of this field" computation.  All in CLOSED FORM over the entry
state; EVM untouched.

Self-contained: does not mention `block_8835311816514709948_concrete_of_code`.
-/
def A_block_8835311816514709948 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_6" ↦ Fin.land (s₀["split_expr_4"]!!) (s₀["split_expr_5"]!!)⟧
          ⟦"split_expr_7" ↦
            (s₀["pos"]!!) + Fin.land (s₀["split_expr_4"]!!) (s₀["split_expr_5"]!!)⟧
          ⟦"end_clear_sanitised_hrafn" ↦
            (s₀["pos"]!!) + Fin.land (s₀["split_expr_4"]!!) (s₀["split_expr_5"]!!) + 32⟧

lemma block_8835311816514709948_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8835311816514709948_concrete_of_code s₀ s₉ →
  Spec A_block_8835311816514709948 s₀ s₉ := by
  unfold block_8835311816514709948_concrete_of_code A_block_8835311816514709948
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common
