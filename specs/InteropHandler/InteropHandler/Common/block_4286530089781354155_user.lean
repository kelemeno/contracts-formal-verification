import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_4286530089781354155_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_22 := not(79228162514264337593543950335)
      value_1          := and(split_expr_21, split_expr_22) }

`not(2^96 - 1)` is the complement of the low-96-bit mask, so `value_1` is
`split_expr_21` with its low 96 bits CLEARED — the standard clear-then-write step
for a packed storage slot.  Given in CLOSED FORM over the entry state.

Self-contained: does not mention `block_4286530089781354155_concrete_of_code`.
-/
def A_block_4286530089781354155 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_22" ↦ UInt256.lnot (79228162514264337593543950335 : UInt256)⟧
          ⟦"value_1" ↦ Fin.land (s₀["split_expr_21"]!!)
              (UInt256.lnot (79228162514264337593543950335 : UInt256))⟧

lemma block_4286530089781354155_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4286530089781354155_concrete_of_code s₀ s₉ →
  Spec A_block_4286530089781354155 s₀ s₉ := by
  unfold block_4286530089781354155_concrete_of_code A_block_4286530089781354155
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  try simp only [multifill_cons, multifill_nil] at hc
  repeat first
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common
