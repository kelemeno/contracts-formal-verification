import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_3582698578014478378_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM: `setEvm` touches only
the machine state, never the variable store. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!
  rcases s <;> rfl

/--
Abstract spec for the Yul block

    {
      mstore(68, split_expr_7)
      revert(0, 100)
    }

Straight-line effects followed by a terminator: the block REVERTS over the shown memory window, so `s₉.evm.reverted = true`.  Bound
variables are in CLOSED FORM over the entry state; the memory/storage effect is
the composed chain in source order.

Self-contained: does not mention `block_3582698578014478378_concrete_of_code`.
-/
def A_block_3582698578014478378 (s₀ s₉ : State) : Prop :=
  s₉ = ((s₀🇪⟦(s₀.evm.mstore (68 : UInt256) (s₀["split_expr_7"]!!))⟧)🇪⟦(s₀🇪⟦(s₀.evm.mstore (68 : UInt256) (s₀["split_expr_7"]!!))⟧).evm.evm_revert (0 : UInt256) (100 : UInt256)⟧) ∧ s₉.evm.reverted = true

lemma block_3582698578014478378_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3582698578014478378_concrete_of_code s₀ s₉ →
  Spec A_block_3582698578014478378 s₀ s₉ := by
  unfold block_3582698578014478378_concrete_of_code A_block_3582698578014478378
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_setEvm] at hc
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  refine ⟨hc.symm, ?_⟩
  rw [← hc]
  rfl

end

end InteropHandler.Common
