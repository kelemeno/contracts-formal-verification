import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_3102284747034715823_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM: `setEvm` touches only
the machine state, never the variable store.  Clear does not ship this; it is what
lets a multi-effect block's variable reads normalize back to the entry state. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!
  rcases s <;> rfl

/--
Abstract spec for the Yul block

    {
      let _9 := mload(_4)
      let expr_mpos := mload(64)
      let _10 := add(expr_mpos, 32)
      mstore(_10, _9)
      let split_expr_84 := add(expr_mpos, 64)
    }

A straight-line block combining memory/storage reads and writes.  Bound variables
are given in CLOSED FORM over the entry state, with each read taken against the
EVM AS OF THAT POINT (so reads see the writes that precede them), and the whole
memory/storage effect is a single `setEvm` carrying the composed chain in source
order.  Nothing else moves.

Self-contained: does not mention `block_3102284747034715823_concrete_of_code`.
-/
def A_block_3102284747034715823 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀⟦"_9" ↦ (s₀.evm.mload (s₀["_4"]!!))⟧)⟦"expr_mpos" ↦ (s₀.evm.mload (64 : UInt256))⟧)⟦"_10" ↦ (s₀.evm.mload (64 : UInt256)) + (32 : UInt256)⟧)⟦"split_expr_84" ↦ (s₀.evm.mload (64 : UInt256)) + (64 : UInt256)⟧)🇪⟦(s₀.evm.mstore ((s₀.evm.mload (64 : UInt256)) + (32 : UInt256)) (s₀.evm.mload (s₀["_4"]!!)))⟧)

lemma block_3102284747034715823_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3102284747034715823_concrete_of_code s₀ s₉ →
  Spec A_block_3102284747034715823 s₀ s₉ := by
  unfold block_3102284747034715823_concrete_of_code A_block_3102284747034715823
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
  try rfl
  exact hc.symm

end

end InteropHandler.Common
