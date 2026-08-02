import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_1667079152629883432_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM: `setEvm` touches only
the machine state, never the variable store.  Clear does not ship this, and it is
what lets a multi-effect block's variable reads be normalized back to the entry
state. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!
  rcases s <;> rfl

/--
Abstract spec for the Yul block

    {
      mstore(memPtr_1, 96)
      let split_expr_5 := add(memPtr_1, 32)
      mstore(split_expr_5, 96)
      let split_expr_6 := add(memPtr_1, 64)
      mstore(split_expr_6, 0)
    }

A straight-line block with 3 memory writes.  Written in LINEAR form:
the bound variables are inserts in CLOSED FORM over the entry state, and the
memory effect is a single `setEvm` carrying the composed chain of `mstore`s in
source order.  Nothing else moves.

Self-contained: does not mention `block_1667079152629883432_concrete_of_code`.
-/
def A_block_1667079152629883432 (s₀ s₉ : State) : Prop :=
  s₉ = (((s₀⟦"split_expr_5" ↦ (s₀["memPtr_1"]!!) + (32 : UInt256)⟧)⟦"split_expr_6" ↦ (s₀["memPtr_1"]!!) + (64 : UInt256)⟧)🇪⟦(((s₀.evm.mstore (s₀["memPtr_1"]!!) (96 : UInt256)).mstore ((s₀["memPtr_1"]!!) + (32 : UInt256)) (96 : UInt256)).mstore ((s₀["memPtr_1"]!!) + (64 : UInt256)) (0 : UInt256))⟧)

lemma block_1667079152629883432_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1667079152629883432_concrete_of_code s₀ s₉ →
  Spec A_block_1667079152629883432 s₀ s₉ := by
  unfold block_1667079152629883432_concrete_of_code A_block_1667079152629883432
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
