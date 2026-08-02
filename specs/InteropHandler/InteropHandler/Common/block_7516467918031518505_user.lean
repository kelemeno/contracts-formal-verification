import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7516467918031518505_gen


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
      let split_expr_7 := add(memPtr_1, 96)
      mstore(split_expr_7, 0)
      let split_expr_8 := add(memPtr, 192)
      mstore(split_expr_8, memPtr_1)
      let split_expr_9 := mload(var_bundle_680_mpos)
    }

A straight-line block combining memory/storage reads and writes.  Bound variables
are given in CLOSED FORM over the entry state, with each read taken against the
EVM AS OF THAT POINT (so reads see the writes that precede them), and the whole
memory/storage effect is a single `setEvm` carrying the composed chain in source
order.  Nothing else moves.

Self-contained: does not mention `block_7516467918031518505_concrete_of_code`.
-/
def A_block_7516467918031518505 (s₀ s₉ : State) : Prop :=
  s₉ = ((((s₀⟦"split_expr_7" ↦ (s₀["memPtr_1"]!!) + (96 : UInt256)⟧)⟦"split_expr_8" ↦ (s₀["memPtr"]!!) + (192 : UInt256)⟧)⟦"split_expr_9" ↦ (((s₀.evm.mstore ((s₀["memPtr_1"]!!) + (96 : UInt256)) (0 : UInt256)).mstore ((s₀["memPtr"]!!) + (192 : UInt256)) (s₀["memPtr_1"]!!)).mload (s₀["var_bundle_680_mpos"]!!))⟧)🇪⟦((s₀.evm.mstore ((s₀["memPtr_1"]!!) + (96 : UInt256)) (0 : UInt256)).mstore ((s₀["memPtr"]!!) + (192 : UInt256)) (s₀["memPtr_1"]!!))⟧)

lemma block_7516467918031518505_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7516467918031518505_concrete_of_code s₀ s₉ →
  Spec A_block_7516467918031518505 s₀ s₉ := by
  unfold block_7516467918031518505_concrete_of_code A_block_7516467918031518505
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
