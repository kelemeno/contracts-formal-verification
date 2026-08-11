import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_3157764704621451027_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { log2(0, 0, 0x2f379..., var__bundleHash) }

The `BundleVerified` event emission.  Clear models `log2` as a complete no-op —
`PrimOps.EVMLog2' : primCall s .Log2 [a, b, c, d] = (s, [])` — so the block
changes NOTHING: no storage, no memory, no bindings.

That is the honest spec, and it is worth stating rather than leaving `sorry`:
a reader of `fun_verifyBundle` needs to know the event emission cannot
interfere with the status write that precedes it, and "the model does not
observe logs" is exactly why.  A consequence worth being explicit about: this
spec says nothing about whether the RIGHT event is emitted, because the model
carries no log state to say it about.

Self-contained: does not mention `block_3157764704621451027_concrete_of_code`.
-/
def A_block_3157764704621451027 (s₀ s₉ : State) : Prop := s₉ = s₀

lemma block_3157764704621451027_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3157764704621451027_concrete_of_code s₀ s₉ →
  Spec A_block_3157764704621451027 s₀ s₉ := by
  unfold block_3157764704621451027_concrete_of_code A_block_3157764704621451027
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  exact hc.symm

end

end InteropHandler.Common
