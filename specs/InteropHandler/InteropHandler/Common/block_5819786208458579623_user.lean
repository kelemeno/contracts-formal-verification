import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_5819786208458579623_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { value_1 := and(_1, split_expr_16) }

Clear's `PrimOps` gives `And [a,b] = Fin.land a b`, so the block binds `value_1`
to the bitwise AND of its operands (the standard mask step) and changes nothing
else.

Self-contained: does not mention `block_5819786208458579623_concrete_of_code`.
-/
def A_block_5819786208458579623 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"value_1" ↦ Fin.land (s₀["_1"]!!) (s₀["split_expr_16"]!!)⟧

lemma block_5819786208458579623_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5819786208458579623_concrete_of_code s₀ s₉ →
  Spec A_block_5819786208458579623 s₀ s₉ := by
  unfold block_5819786208458579623_concrete_of_code A_block_5819786208458579623
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
