import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_1885029154092524249_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { revert(0, 100) }

An UNCONDITIONAL revert over the 100-byte memory window at 0 (a 4-byte selector
plus three words of error payload): the EVM is replaced by `evm_revert evm 0 100`,
so `s₉.evm.reverted = true`.

Self-contained: does not mention `block_1885029154092524249_concrete_of_code`.
-/
def A_block_1885029154092524249 (s₀ s₉ : State) : Prop :=
  s₉ = s₀🇪⟦s₀.evm.evm_revert 0 100⟧ ∧ s₉.evm.reverted = true

lemma block_1885029154092524249_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1885029154092524249_concrete_of_code s₀ s₉ →
  Spec A_block_1885029154092524249 s₀ s₉ := by
  unfold block_1885029154092524249_concrete_of_code A_block_1885029154092524249
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  refine ⟨hc.symm, ?_⟩
  rw [← hc]
  rfl

end

end InteropHandler.Common
