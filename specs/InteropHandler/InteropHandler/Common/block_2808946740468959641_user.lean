import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2808946740468959641_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let cleaned      := and(split_expr_2, split_expr_4)
      let split_expr_5 := eq(cleaned, sum) }

Masks `split_expr_2` with `split_expr_4`, then compares the result against `sum`;
`split_expr_5` is the equality flag (`1` if equal, `0` otherwise).  Both values
are given in CLOSED FORM over the entry state.

This is the mask-and-compare that AUTHENTICATES a message sender against a
constant address: `split_expr_4` is the 160-bit address mask and `sum` the
expected constant, so `split_expr_5` is precisely the "sender is authorised" bit
that the following guard block branches on.

Self-contained: does not mention `block_2808946740468959641_concrete_of_code`.
-/
def A_block_2808946740468959641 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"cleaned" ↦ Fin.land (s₀["split_expr_2"]!!) (s₀["split_expr_4"]!!)⟧
          ⟦"split_expr_5" ↦
            (if Fin.land (s₀["split_expr_2"]!!) (s₀["split_expr_4"]!!) = (s₀["sum"]!!)
             then (1 : UInt256) else 0)⟧

lemma block_2808946740468959641_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2808946740468959641_concrete_of_code s₀ s₉ →
  Spec A_block_2808946740468959641 s₀ s₉ := by
  unfold block_2808946740468959641_concrete_of_code A_block_2808946740468959641
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common
