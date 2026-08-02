import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_5731116343986243113_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_4 := slt(rel_offset_of_tail, split_expr_3) }

Clear's `PrimOps` gives `Slt [a,b] = fromBool (UInt256.slt a b)`, so the block binds `split_expr_4` to that comparison flag
(`1` when it holds, `0` otherwise) and changes nothing else: the EVM is untouched
and every other variable keeps its value.

Self-contained: does not mention `block_5731116343986243113_concrete_of_code`.
-/
def A_block_5731116343986243113 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_4" ↦
      (if UInt256.slt (s₀["rel_offset_of_tail"]!!) (s₀["split_expr_3"]!!) = true then (1 : UInt256) else 0)⟧

lemma block_5731116343986243113_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5731116343986243113_concrete_of_code s₀ s₉ →
  Spec A_block_5731116343986243113 s₀ s₉ := by
  unfold block_5731116343986243113_concrete_of_code A_block_5731116343986243113
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
