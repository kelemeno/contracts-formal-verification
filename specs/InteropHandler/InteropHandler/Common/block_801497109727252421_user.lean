import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_801497109727252421_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let split_expr_0 := add(size, 31)
      let split_expr_1 := not(31)
      let split_expr_2 := and(split_expr_0, split_expr_1)
      let newFreePtr := add(memPtr, split_expr_2)
      let split_expr_3 := gt(newFreePtr, 18446744073709551615)
    }

A pure straight-line computation: each bound variable is given in CLOSED FORM
over the entry state (intermediate bindings substituted away), the EVM is
untouched, and no other variable moves.

Self-contained: does not mention `block_801497109727252421_concrete_of_code`.
-/
def A_block_801497109727252421 (s₀ s₉ : State) : Prop :=
  s₉ = s₀
          ⟦"split_expr_0" ↦ (s₀["size"]!!) + (31 : UInt256)⟧
          ⟦"split_expr_1" ↦ UInt256.lnot (31 : UInt256)⟧
          ⟦"split_expr_2" ↦ Fin.land ((s₀["size"]!!) + (31 : UInt256)) (UInt256.lnot (31 : UInt256))⟧
          ⟦"newFreePtr" ↦ (s₀["memPtr"]!!) + (Fin.land ((s₀["size"]!!) + (31 : UInt256)) (UInt256.lnot (31 : UInt256)))⟧
          ⟦"split_expr_3" ↦ (if ((s₀["memPtr"]!!) + (Fin.land ((s₀["size"]!!) + (31 : UInt256)) (UInt256.lnot (31 : UInt256)))) > (18446744073709551615 : UInt256) then (1 : UInt256) else 0)⟧

lemma block_801497109727252421_abs_of_concrete {s₀ s₉ : State} :
  Spec block_801497109727252421_concrete_of_code s₀ s₉ →
  Spec A_block_801497109727252421 s₀ s₉ := by
  unfold block_801497109727252421_concrete_of_code A_block_801497109727252421
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
