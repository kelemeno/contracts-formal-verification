import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_4481893504431727677_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { var_7138_mpos := memPtr }

A pure variable copy: `var_7138_mpos` takes the value of `memPtr`, nothing else
moves.

Self-contained: does not mention `block_4481893504431727677_concrete_of_code`.
-/
def A_block_4481893504431727677 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"var_7138_mpos" ↦ (s₀["memPtr"]!!)⟧

lemma block_4481893504431727677_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4481893504431727677_concrete_of_code s₀ s₉ →
  Spec A_block_4481893504431727677 s₀ s₉ := by
  unfold block_4481893504431727677_concrete_of_code A_block_4481893504431727677
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
