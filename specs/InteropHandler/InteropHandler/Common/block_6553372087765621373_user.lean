import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6553372087765621373_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_18 := eq(var_self_length, sum) }

Clear's `PrimOps` gives `Eq [a,b] = fromBool (a = b)`, so the block binds `split_expr_18` to that comparison flag
(`1` when it holds, `0` otherwise) and changes nothing else: the EVM is untouched
and every other variable keeps its value.

Self-contained: does not mention `block_6553372087765621373_concrete_of_code`.
-/
def A_block_6553372087765621373 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_18" ↦
      (if (s₀["var_self_length"]!!) = (s₀["sum"]!!) then (1 : UInt256) else 0)⟧

lemma block_6553372087765621373_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6553372087765621373_concrete_of_code s₀ s₉ →
  Spec A_block_6553372087765621373 s₀ s₉ := by
  unfold block_6553372087765621373_concrete_of_code A_block_6553372087765621373
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
