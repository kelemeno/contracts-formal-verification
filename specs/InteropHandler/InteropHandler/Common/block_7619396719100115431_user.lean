import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7619396719100115431_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_38 := add(split_expr_37, 4)
      let srcEnd        := add(split_expr_38, 32) }

A pure arithmetic chain, given in CLOSED FORM over the entry state: skip a 4-byte
selector, then advance one word to the end of the first argument.  EVM untouched,
no other variable moves.

Self-contained: does not mention `block_7619396719100115431_concrete_of_code`.
-/
def A_block_7619396719100115431 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_38" ↦ (s₀["split_expr_37"]!!) + 4⟧
          ⟦"srcEnd" ↦ (s₀["split_expr_37"]!!) + 4 + 32⟧

lemma block_7619396719100115431_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7619396719100115431_concrete_of_code s₀ s₉ →
  Spec A_block_7619396719100115431 s₀ s₉ := by
  unfold block_7619396719100115431_concrete_of_code A_block_7619396719100115431
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  rw [lookup_insert] at hc
  exact hc.symm

end

end InteropHandler.Common
