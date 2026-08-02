import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2435830699431932975_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_16 := and(split_expr_14, split_expr_15)
      let split_expr_17 := shl(248, 1)
      let split_expr_18 := eq(split_expr_16, split_expr_17) }

Masks `split_expr_14`, builds the constant `1 << 248` (top byte set), and
compares: `split_expr_18` is a single-byte tag test.  All in CLOSED FORM over the
entry state; EVM untouched.

Self-contained: does not mention `block_2435830699431932975_concrete_of_code`.
-/
def A_block_2435830699431932975 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_16" ↦ Fin.land (s₀["split_expr_14"]!!) (s₀["split_expr_15"]!!)⟧
          ⟦"split_expr_17" ↦ Fin.shiftLeft (1 : UInt256) 248⟧
          ⟦"split_expr_18" ↦
            (if Fin.land (s₀["split_expr_14"]!!) (s₀["split_expr_15"]!!)
                  = Fin.shiftLeft (1 : UInt256) 248
             then (1 : UInt256) else 0)⟧

lemma block_2435830699431932975_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2435830699431932975_concrete_of_code s₀ s₉ →
  Spec A_block_2435830699431932975 s₀ s₉ := by
  unfold block_2435830699431932975_concrete_of_code A_block_2435830699431932975
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
