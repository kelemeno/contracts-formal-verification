import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2108987349013167502_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_24 := extcodesize(_5) }

Binds `split_expr_24` to the code size of the address in `_5` and changes nothing
else — `extcodesize` is a pure read in Clear's model
(`PrimOps.EVMExtcodesize' : primCall s .Extcodesize [a] = (s, [s.evm.extCodeSize a])`),
so the EVM is untouched.

Self-contained: does not mention `block_2108987349013167502_concrete_of_code`.
-/
def A_block_2108987349013167502 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_24" ↦ s₀.evm.extCodeSize (s₀["_5"]!!)⟧

lemma block_2108987349013167502_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2108987349013167502_concrete_of_code s₀ s₉ →
  Spec A_block_2108987349013167502 s₀ s₉ := by
  unfold block_2108987349013167502_concrete_of_code A_block_2108987349013167502
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
