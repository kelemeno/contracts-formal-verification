import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7356270655256221062_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_25 := add(_1, _5)
      let expr_7        := add(split_expr_25, 6)
      let split_expr_26 := eq(expr_6, expr_7) }

Computes a base-plus-offset pointer, advances it by 6, and compares against
`expr_6`; `split_expr_26` is the equality flag — a length/consistency check.
All in CLOSED FORM over the entry state; EVM untouched.

Self-contained: does not mention `block_7356270655256221062_concrete_of_code`.
-/
def A_block_7356270655256221062 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_25" ↦ (s₀["_1"]!!) + (s₀["_5"]!!)⟧
          ⟦"expr_7" ↦ (s₀["_1"]!!) + (s₀["_5"]!!) + 6⟧
          ⟦"split_expr_26" ↦
            (if (s₀["expr_6"]!!) = (s₀["_1"]!!) + (s₀["_5"]!!) + 6
             then (1 : UInt256) else 0)⟧

lemma block_7356270655256221062_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7356270655256221062_concrete_of_code s₀ s₉ →
  Spec A_block_7356270655256221062 s₀ s₉ := by
  unfold block_7356270655256221062_concrete_of_code A_block_7356270655256221062
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
