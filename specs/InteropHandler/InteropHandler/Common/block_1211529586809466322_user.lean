import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_1211529586809466322_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_5 := eq(split_expr_3, split_expr_4) }

Clear's `PrimOps` gives `Eq [a,b] = fromBool (a = b)`, so the block binds `split_expr_5`
to the equality flag of its two operands and changes nothing else — the EVM is
untouched and every other variable keeps its value.

Self-contained: does not mention `block_1211529586809466322_concrete_of_code`.
-/
def A_block_1211529586809466322 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_5" ↦
      (if (s₀["split_expr_3"]!!) = (s₀["split_expr_4"]!!) then (1 : UInt256) else 0)⟧

lemma block_1211529586809466322_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1211529586809466322_concrete_of_code s₀ s₉ →
  Spec A_block_1211529586809466322 s₀ s₉ := by
  unfold block_1211529586809466322_concrete_of_code A_block_1211529586809466322
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
