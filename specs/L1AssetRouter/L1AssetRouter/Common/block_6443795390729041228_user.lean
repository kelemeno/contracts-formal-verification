import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_6443795390729041228_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Middle block of `abi_encode_bytes`: zero the padding word past the payload, and compute
the two operands of the round-up.

    let split_expr_2 := add(pos, length)
    let split_expr_3 := add(split_expr_2, 32)
    mstore(split_expr_3, 0)              -- zero the tail so padding is deterministic
    let split_expr_4 := add(length, 31)
    let split_expr_5 := not(31)

The `mstore(.., 0)` is why `BundleHashEncoding.pad32` can pad with zeros rather than junk. -/
def A_block_6443795390729041228 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"split_expr_2" ↦ (s₀["pos"]!! + (s₀["length"]!!))⟧
  let b := a⟦"split_expr_3" ↦ (a["split_expr_2"]!! + 32)⟧
  let c := b🇪⟦EVMState.mstore s₀.evm (b["split_expr_3"]!!) 0⟧
  let d := c⟦"split_expr_4" ↦ (c["length"]!! + 31)⟧
  s₉ = d⟦"split_expr_5" ↦ Clear.UInt256.lnot 31⟧

lemma block_6443795390729041228_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6443795390729041228_concrete_of_code s₀ s₉ →
  Spec A_block_6443795390729041228 s₀ s₉ := by
  unfold block_6443795390729041228_concrete_of_code A_block_6443795390729041228
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
end

end L1AssetRouter.Common
