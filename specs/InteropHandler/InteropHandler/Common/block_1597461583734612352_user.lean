import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_1597461583734612352_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { mstore(dst, memPtr_4)
      dst := add(dst, 32) }

One word is written to memory at the cursor `dst`, then the cursor advances by
one word.  Both effects in CLOSED FORM over the entry state: the EVM gains
exactly the single `mstore` at the OLD `dst`, and the only variable that moves is
`dst`.  This is the copy-loop body step.

Self-contained: does not mention `block_1597461583734612352_concrete_of_code`.
-/
def A_block_1597461583734612352 (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦s₀.evm.mstore (s₀["dst"]!!) (s₀["memPtr_4"]!!)⟧)⟦"dst" ↦ (s₀["dst"]!!) + 32⟧

lemma block_1597461583734612352_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1597461583734612352_concrete_of_code s₀ s₉ →
  Spec A_block_1597461583734612352 s₀ s₉ := by
  unfold block_1597461583734612352_concrete_of_code A_block_1597461583734612352
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common
