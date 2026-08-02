import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_4336215878172870242_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let split_expr_19 := add(var_self_offset, _1)
      offsetOut := add(split_expr_19, 6)
      let split_expr_20 := sub(_2, _1)
      let split_expr_21 := not(5)
      let split_expr_22 := add(split_expr_20, split_expr_21)
    }

A pure straight-line computation: each bound variable is given in CLOSED FORM
over the entry state (intermediate bindings substituted away), the EVM is
untouched, and no other variable moves.

Self-contained: does not mention `block_4336215878172870242_concrete_of_code`.
-/
def A_block_4336215878172870242 (s₀ s₉ : State) : Prop :=
  s₉ = s₀
          ⟦"split_expr_19" ↦ (s₀["var_self_offset"]!!) + (s₀["_1"]!!)⟧
          ⟦"offsetOut" ↦ ((s₀["var_self_offset"]!!) + (s₀["_1"]!!)) + (6 : UInt256)⟧
          ⟦"split_expr_20" ↦ (s₀["_2"]!!) - (s₀["_1"]!!)⟧
          ⟦"split_expr_21" ↦ UInt256.lnot (5 : UInt256)⟧
          ⟦"split_expr_22" ↦ ((s₀["_2"]!!) - (s₀["_1"]!!)) + (UInt256.lnot (5 : UInt256))⟧

lemma block_4336215878172870242_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4336215878172870242_concrete_of_code s₀ s₉ →
  Spec A_block_4336215878172870242 s₀ s₉ := by
  unfold block_4336215878172870242_concrete_of_code A_block_4336215878172870242
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
