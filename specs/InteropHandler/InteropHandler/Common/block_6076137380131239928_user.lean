import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6076137380131239928_gen


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
      mstore(split_expr_24, memPtr_1)
      let split_expr_25 := add(_1, 128)
      let offset_4 := calldataload(split_expr_25)
    }

A straight-line block over memory/storage/calldata and the execution
environment.  Each bound variable is in CLOSED FORM over the entry state, with
reads taken against the EVM AS OF THAT POINT, and the whole effect is one
`setEvm` carrying the composed chain in source order.  Nothing else moves.

Self-contained: does not mention `block_6076137380131239928_concrete_of_code`.
-/
def A_block_6076137380131239928 (s₀ s₉ : State) : Prop :=
  s₉ = (((s₀⟦"split_expr_25" ↦ (s₀["_1"]!!) + (128 : UInt256)⟧)⟦"offset_4" ↦ ((s₀.evm.mstore (s₀["split_expr_24"]!!) (s₀["memPtr_1"]!!)).calldataload ((s₀["_1"]!!) + (128 : UInt256)))⟧)🇪⟦(s₀.evm.mstore (s₀["split_expr_24"]!!) (s₀["memPtr_1"]!!))⟧)

lemma block_6076137380131239928_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6076137380131239928_concrete_of_code s₀ s₉ →
  Spec A_block_6076137380131239928 s₀ s₉ := by
  unfold block_6076137380131239928_concrete_of_code A_block_6076137380131239928
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
