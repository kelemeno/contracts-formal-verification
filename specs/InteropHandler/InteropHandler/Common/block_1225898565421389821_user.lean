import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_1225898565421389821_gen


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
      let split_expr_76 := mload(split_expr_75)
      mstore(split_expr_74, split_expr_76)
      let split_expr_77 := add(memPtr_2, 192)
      mstore(split_expr_77, memPtr_5)
      var_interopBundle_684_mpos := memPtr_2
    }

A straight-line block combining memory/storage reads and writes.  Bound variables
are given in CLOSED FORM over the entry state, with each read taken against the
EVM AS OF THAT POINT (so reads see the writes that precede them), and the whole
memory/storage effect is a single `setEvm` carrying the composed chain in source
order.  Nothing else moves.

Self-contained: does not mention `block_1225898565421389821_concrete_of_code`.
-/
def A_block_1225898565421389821 (s₀ s₉ : State) : Prop :=
  s₉ = ((((s₀⟦"split_expr_76" ↦ (s₀.evm.mload (s₀["split_expr_75"]!!))⟧)⟦"split_expr_77" ↦ (s₀["memPtr_2"]!!) + (192 : UInt256)⟧)⟦"var_interopBundle_684_mpos" ↦ (s₀["memPtr_2"]!!)⟧)🇪⟦((s₀.evm.mstore (s₀["split_expr_74"]!!) (s₀.evm.mload (s₀["split_expr_75"]!!))).mstore ((s₀["memPtr_2"]!!) + (192 : UInt256)) (s₀["memPtr_5"]!!))⟧)

lemma block_1225898565421389821_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1225898565421389821_concrete_of_code s₀ s₉ →
  Spec A_block_1225898565421389821 s₀ s₉ := by
  unfold block_1225898565421389821_concrete_of_code A_block_1225898565421389821
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
