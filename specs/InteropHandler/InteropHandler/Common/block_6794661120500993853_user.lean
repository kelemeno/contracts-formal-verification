import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6794661120500993853_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { var_3555_mpos := expr_3580_mpos }

A pure variable copy: `var_3555_mpos` takes the value of `expr_3580_mpos`,
nothing else moves.

Self-contained: does not mention `block_6794661120500993853_concrete_of_code`.
-/
def A_block_6794661120500993853 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"var_3555_mpos" ↦ (s₀["expr_3580_mpos"]!!)⟧

lemma block_6794661120500993853_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6794661120500993853_concrete_of_code s₀ s₉ →
  Spec A_block_6794661120500993853 s₀ s₉ := by
  unfold block_6794661120500993853_concrete_of_code A_block_6794661120500993853
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
