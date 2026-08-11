import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_8261716617869206867_gen


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
      let outPtr := mload(64)
      let split_expr_7 := add(outPtr, 32)
      let split_expr_8 := shl(248, 1)
      mstore(split_expr_7, split_expr_8)
      let length := mload(var_bundle_mpos)
    }

Writes the one-byte tag `1 << 248` at `outPtr + 32` and binds the four locals.
`length` is read AFTER the store, so it is taken against the post-store EVM —
which matters, since nothing here rules out `var_bundle_mpos` aliasing
`outPtr + 32`.

The `shl(248, 1)` is carried symbolically; it is never evaluated.  This block was
previously filed under the large-shift blocker (`AGENTS.md` gap 2), which is
partly disproved — see that entry.

Self-contained: does not mention `block_8261716617869206867_concrete_of_code`.
-/
def A_block_8261716617869206867 (s₀ s₉ : State) : Prop :=
  s₉ = ((((s₀⟦"outPtr" ↦ s₀.evm.mload 64⟧)⟦"split_expr_7" ↦ (s₀.evm.mload 64) + (32 : UInt256)⟧)⟦"split_expr_8" ↦ Fin.shiftLeft (1 : UInt256) 248⟧)⟦"length" ↦ (s₀.evm.mstore ((s₀.evm.mload 64) + (32 : UInt256)) (Fin.shiftLeft (1 : UInt256) 248)).mload (s₀["var_bundle_mpos"]!!)⟧)🇪⟦(s₀.evm.mstore ((s₀.evm.mload 64) + (32 : UInt256)) (Fin.shiftLeft (1 : UInt256) 248))⟧

lemma block_8261716617869206867_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8261716617869206867_concrete_of_code s₀ s₉ →
  Spec A_block_8261716617869206867 s₀ s₉ := by
  unfold block_8261716617869206867_concrete_of_code A_block_8261716617869206867
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
