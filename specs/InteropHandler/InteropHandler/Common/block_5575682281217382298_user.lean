import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_5575682281217382298_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!
  rcases s <;> rfl

/--
Abstract spec for the Yul block

    {
      let split_expr_19 := add(var_proof_mpos, 128)
      let _385_mpos := mload(split_expr_19)
      let _9 := mload(64)
      let split_expr_20 := shl(225, 207355409)
      mstore(_9, split_expr_20)
    }

Loads the proof's field at offset 128 and the free pointer, then writes a
selector word at the free pointer.  Both `mload`s precede the store, so unlike
`block_8261716617869206867` every read here is against the ENTRY evm.

`shl(225, 207355409)` is carried symbolically; it is never evaluated.

Self-contained: does not mention `block_5575682281217382298_concrete_of_code`.
-/
def A_block_5575682281217382298 (s₀ s₉ : State) : Prop :=
  s₉ = ((((s₀⟦"split_expr_19" ↦ (s₀["var_proof_mpos"]!!) + (128 : UInt256)⟧)⟦"_385_mpos" ↦ s₀.evm.mload ((s₀["var_proof_mpos"]!!) + (128 : UInt256))⟧)⟦"_9" ↦ s₀.evm.mload 64⟧)⟦"split_expr_20" ↦ Fin.shiftLeft (207355409 : UInt256) 225⟧)🇪⟦(s₀.evm.mstore (s₀.evm.mload 64) (Fin.shiftLeft (207355409 : UInt256) 225))⟧

lemma block_5575682281217382298_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5575682281217382298_concrete_of_code s₀ s₉ →
  Spec A_block_5575682281217382298 s₀ s₉ := by
  unfold block_5575682281217382298_concrete_of_code A_block_5575682281217382298
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
