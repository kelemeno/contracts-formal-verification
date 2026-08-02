import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7346920477424193670_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let split_expr_17 := sub(20, length_1)
      let split_expr_18 := shl(3, split_expr_17)
      let split_expr_19 := not(79228162514264337593543950335)
      let split_expr_20 := shl(split_expr_18, split_expr_19)
      let split_expr_21 := and(_1, split_expr_20)
    }

A pure straight-line computation: each bound variable is given in CLOSED FORM
over the entry state (intermediate bindings substituted away), the EVM is
untouched, and no other variable moves.

Self-contained: does not mention `block_7346920477424193670_concrete_of_code`.
-/
def A_block_7346920477424193670 (s₀ s₉ : State) : Prop :=
  s₉ = s₀
          ⟦"split_expr_17" ↦ (20 : UInt256) - (s₀["length_1"]!!)⟧
          ⟦"split_expr_18" ↦ Fin.shiftLeft ((20 : UInt256) - (s₀["length_1"]!!)) (3 : UInt256)⟧
          ⟦"split_expr_19" ↦ UInt256.lnot (79228162514264337593543950335 : UInt256)⟧
          ⟦"split_expr_20" ↦ Fin.shiftLeft (UInt256.lnot (79228162514264337593543950335 : UInt256)) (Fin.shiftLeft ((20 : UInt256) - (s₀["length_1"]!!)) (3 : UInt256))⟧
          ⟦"split_expr_21" ↦ Fin.land (s₀["_1"]!!) (Fin.shiftLeft (UInt256.lnot (79228162514264337593543950335 : UInt256)) (Fin.shiftLeft ((20 : UInt256) - (s₀["length_1"]!!)) (3 : UInt256)))⟧

lemma block_7346920477424193670_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7346920477424193670_concrete_of_code s₀ s₉ →
  Spec A_block_7346920477424193670 s₀ s₉ := by
  unfold block_7346920477424193670_concrete_of_code A_block_7346920477424193670
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
