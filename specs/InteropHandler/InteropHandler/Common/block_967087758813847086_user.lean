import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_967087758813847086_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let split_expr_26 := add(_9, 132)
      let split_expr_27 := sub(tail, _9)
      let split_expr_28 := not(3)
      let split_expr_29 := add(split_expr_27, split_expr_28)
      mstore(split_expr_26, split_expr_29)
    }

A straight-line block: pure computations plus a single memory write.  Every
bound variable is in CLOSED FORM over the entry state and the EVM gains exactly
the one `mstore` shown; nothing else moves.

Self-contained: does not mention `block_967087758813847086_concrete_of_code`.
-/
def A_block_967087758813847086 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀⟦"split_expr_26" ↦ (s₀["_9"]!!) + (132 : UInt256)⟧)⟦"split_expr_27" ↦ (s₀["tail"]!!) - (s₀["_9"]!!)⟧)⟦"split_expr_28" ↦ UInt256.lnot (3 : UInt256)⟧)⟦"split_expr_29" ↦ ((s₀["tail"]!!) - (s₀["_9"]!!)) + (UInt256.lnot (3 : UInt256))⟧)🇪⟦((((s₀⟦"split_expr_26" ↦ (s₀["_9"]!!) + (132 : UInt256)⟧)⟦"split_expr_27" ↦ (s₀["tail"]!!) - (s₀["_9"]!!)⟧)⟦"split_expr_28" ↦ UInt256.lnot (3 : UInt256)⟧)⟦"split_expr_29" ↦ ((s₀["tail"]!!) - (s₀["_9"]!!)) + (UInt256.lnot (3 : UInt256))⟧).evm.mstore ((s₀["_9"]!!) + (132 : UInt256)) (((s₀["tail"]!!) - (s₀["_9"]!!)) + (UInt256.lnot (3 : UInt256)))⟧)

lemma block_967087758813847086_abs_of_concrete {s₀ s₉ : State} :
  Spec block_967087758813847086_concrete_of_code s₀ s₉ →
  Spec A_block_967087758813847086 s₀ s₉ := by
  unfold block_967087758813847086_concrete_of_code A_block_967087758813847086
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
