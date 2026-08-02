import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_5291704544479297361_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      mstore(split_expr_11, 0)
      let split_expr_12 := sub(_3, outPtr)
      let _4 := add(split_expr_12, 33)
      let split_expr_13 := not(31)
      let split_expr_14 := add(_4, split_expr_13)
    }

A straight-line block: pure computations plus a single memory write.  Every
bound variable is in CLOSED FORM over the entry state and the EVM gains exactly
the one `mstore` shown; nothing else moves.

Self-contained: does not mention `block_5291704544479297361_concrete_of_code`.
-/
def A_block_5291704544479297361 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀🇪⟦s₀.evm.mstore (s₀["split_expr_11"]!!) (0 : UInt256)⟧)⟦"split_expr_12" ↦ (s₀["_3"]!!) - (s₀["outPtr"]!!)⟧)⟦"_4" ↦ ((s₀["_3"]!!) - (s₀["outPtr"]!!)) + (33 : UInt256)⟧)⟦"split_expr_13" ↦ UInt256.lnot (31 : UInt256)⟧)⟦"split_expr_14" ↦ (((s₀["_3"]!!) - (s₀["outPtr"]!!)) + (33 : UInt256)) + (UInt256.lnot (31 : UInt256))⟧)

lemma block_5291704544479297361_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5291704544479297361_concrete_of_code s₀ s₉ →
  Spec A_block_5291704544479297361 s₀ s₉ := by
  unfold block_5291704544479297361_concrete_of_code A_block_5291704544479297361
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
