import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2386757029538874328_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      mstore(memPtr_2, length)
      dst := add(memPtr_2, 32)
      let split_expr_28 := shl(5, length)
      let split_expr_29 := add(_3, split_expr_28)
      let srcEnd := add(split_expr_29, 32)
    }

A straight-line block: pure computations plus a single memory write.  Every
bound variable is in CLOSED FORM over the entry state and the EVM gains exactly
the one `mstore` shown; nothing else moves.

Self-contained: does not mention `block_2386757029538874328_concrete_of_code`.
-/
def A_block_2386757029538874328 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀🇪⟦s₀.evm.mstore (s₀["memPtr_2"]!!) (s₀["length"]!!)⟧)⟦"dst" ↦ (s₀["memPtr_2"]!!) + (32 : UInt256)⟧)⟦"split_expr_28" ↦ Fin.shiftLeft (s₀["length"]!!) (5 : UInt256)⟧)⟦"split_expr_29" ↦ (s₀["_3"]!!) + (Fin.shiftLeft (s₀["length"]!!) (5 : UInt256))⟧)⟦"srcEnd" ↦ ((s₀["_3"]!!) + (Fin.shiftLeft (s₀["length"]!!) (5 : UInt256))) + (32 : UInt256)⟧)

lemma block_2386757029538874328_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2386757029538874328_concrete_of_code s₀ s₉ →
  Spec A_block_2386757029538874328 s₀ s₉ := by
  unfold block_2386757029538874328_concrete_of_code A_block_2386757029538874328
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
