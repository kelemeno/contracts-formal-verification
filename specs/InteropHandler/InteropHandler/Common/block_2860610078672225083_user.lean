import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2860610078672225083_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { end_clear_sanitised_hrafn := add(split_expr_6, 32) }

Binds `end_clear_sanitised_hrafn` to `split_expr_6 + 32` (a 32-byte cursor
advance) and changes nothing else.

Self-contained: does not mention `block_2860610078672225083_concrete_of_code`.
-/
def A_block_2860610078672225083 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"end_clear_sanitised_hrafn" ↦ (s₀["split_expr_6"]!!) + 32⟧

lemma block_2860610078672225083_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2860610078672225083_concrete_of_code s₀ s₉ →
  Spec A_block_2860610078672225083 s₀ s₉ := by
  unfold block_2860610078672225083_concrete_of_code A_block_2860610078672225083
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
