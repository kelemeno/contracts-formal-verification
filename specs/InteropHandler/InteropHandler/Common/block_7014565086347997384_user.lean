import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_7014565086347997384_gen


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
      let split_expr_23 := add(var_self_3703_mpos, expr_3)
      addr := add(split_expr_23, 32)
      let split_expr_24 := mload(addr)
      let _5 := shr(248, split_expr_24)
      let expr_6 := mload(var_self_3703_mpos)
    }

A straight-line block combining memory/storage reads and writes.  Bound variables
are given in CLOSED FORM over the entry state, with each read taken against the
EVM AS OF THAT POINT (so reads see the writes that precede them), and the whole
memory/storage effect is a single `setEvm` carrying the composed chain in source
order.  Nothing else moves.

Self-contained: does not mention `block_7014565086347997384_concrete_of_code`.
-/
def A_block_7014565086347997384 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀⟦"split_expr_23" ↦ (s₀["var_self_3703_mpos"]!!) + (s₀["expr_3"]!!)⟧)⟦"addr" ↦ ((s₀["var_self_3703_mpos"]!!) + (s₀["expr_3"]!!)) + (32 : UInt256)⟧)⟦"split_expr_24" ↦ (s₀.evm.mload (((s₀["var_self_3703_mpos"]!!) + (s₀["expr_3"]!!)) + (32 : UInt256)))⟧)⟦"_5" ↦ Fin.shiftRight (s₀.evm.mload (((s₀["var_self_3703_mpos"]!!) + (s₀["expr_3"]!!)) + (32 : UInt256))) (248 : UInt256)⟧)⟦"expr_6" ↦ (s₀.evm.mload (s₀["var_self_3703_mpos"]!!))⟧)

lemma block_7014565086347997384_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7014565086347997384_concrete_of_code s₀ s₉ →
  Spec A_block_7014565086347997384 s₀ s₉ := by
  unfold block_7014565086347997384_concrete_of_code A_block_7014565086347997384
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
