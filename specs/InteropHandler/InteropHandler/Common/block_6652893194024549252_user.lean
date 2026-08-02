import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6652893194024549252_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_2 := add(offset, length)
      let split_expr_3 := add(split_expr_2, 32) }

A pure two-step arithmetic chain: `split_expr_2` is the end of the `[offset,
length)` region and `split_expr_3` is that end advanced by one word.  Both are
given in CLOSED FORM over the entry state, so the spec does not depend on the
intermediate binding.  The EVM is untouched and no other variable moves.

Self-contained: does not mention `block_6652893194024549252_concrete_of_code`.
-/
def A_block_6652893194024549252 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_2" ↦ (s₀["offset"]!!) + (s₀["length"]!!)⟧
          ⟦"split_expr_3" ↦ (s₀["offset"]!!) + (s₀["length"]!!) + 32⟧

lemma block_6652893194024549252_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6652893194024549252_concrete_of_code s₀ s₉ →
  Spec A_block_6652893194024549252 s₀ s₉ := by
  unfold block_6652893194024549252_concrete_of_code A_block_6652893194024549252
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  rw [lookup_insert] at hc
  exact hc.symm

end

end InteropHandler.Common
