import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6636810931393710079_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      mstore(memPtr, length)
      dst := add(memPtr, 32)
      let split_expr_0 := shl(5, length)
      let srcEnd := add(offset, split_expr_0)
    }

A straight-line block: pure computations plus a single memory write.  Every
bound variable is in CLOSED FORM over the entry state and the EVM gains exactly
the one `mstore` shown; nothing else moves.

Self-contained: does not mention `block_6636810931393710079_concrete_of_code`.
-/
def A_block_6636810931393710079 (s₀ s₉ : State) : Prop :=
  s₉ = ((((s₀🇪⟦s₀.evm.mstore (s₀["memPtr"]!!) (s₀["length"]!!)⟧)⟦"dst" ↦ (s₀["memPtr"]!!) + (32 : UInt256)⟧)⟦"split_expr_0" ↦ Fin.shiftLeft (s₀["length"]!!) (5 : UInt256)⟧)⟦"srcEnd" ↦ (s₀["offset"]!!) + (Fin.shiftLeft (s₀["length"]!!) (5 : UInt256))⟧)

lemma block_6636810931393710079_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6636810931393710079_concrete_of_code s₀ s₉ →
  Spec A_block_6636810931393710079 s₀ s₉ := by
  unfold block_6636810931393710079_concrete_of_code A_block_6636810931393710079
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
