import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_8826415069637874530_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let split_expr_13 := add(expr_3580_mpos, 36)
      let split_expr_14 := shl(248, _1)
      let split_expr_15 := shl(248, 255)
      let split_expr_16 := and(split_expr_14, split_expr_15)
      mstore(split_expr_13, split_expr_16)
    }

A straight-line block: pure computations plus a single memory write.  Every
bound variable is in CLOSED FORM over the entry state and the EVM gains exactly
the one `mstore` shown; nothing else moves.

Self-contained: does not mention `block_8826415069637874530_concrete_of_code`.
-/
def A_block_8826415069637874530 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀⟦"split_expr_13" ↦ (s₀["expr_3580_mpos"]!!) + (36 : UInt256)⟧)⟦"split_expr_14" ↦ Fin.shiftLeft (s₀["_1"]!!) (248 : UInt256)⟧)⟦"split_expr_15" ↦ Fin.shiftLeft (255 : UInt256) (248 : UInt256)⟧)⟦"split_expr_16" ↦ Fin.land (Fin.shiftLeft (s₀["_1"]!!) (248 : UInt256)) (Fin.shiftLeft (255 : UInt256) (248 : UInt256))⟧)🇪⟦((((s₀⟦"split_expr_13" ↦ (s₀["expr_3580_mpos"]!!) + (36 : UInt256)⟧)⟦"split_expr_14" ↦ Fin.shiftLeft (s₀["_1"]!!) (248 : UInt256)⟧)⟦"split_expr_15" ↦ Fin.shiftLeft (255 : UInt256) (248 : UInt256)⟧)⟦"split_expr_16" ↦ Fin.land (Fin.shiftLeft (s₀["_1"]!!) (248 : UInt256)) (Fin.shiftLeft (255 : UInt256) (248 : UInt256))⟧).evm.mstore ((s₀["expr_3580_mpos"]!!) + (36 : UInt256)) (Fin.land (Fin.shiftLeft (s₀["_1"]!!) (248 : UInt256)) (Fin.shiftLeft (255 : UInt256) (248 : UInt256)))⟧)

lemma block_8826415069637874530_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8826415069637874530_concrete_of_code s₀ s₉ →
  Spec A_block_8826415069637874530 s₀ s₉ := by
  unfold block_8826415069637874530_concrete_of_code A_block_8826415069637874530
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
