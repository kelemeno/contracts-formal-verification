import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4451958921457272093_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **THE TREE'S INDEX GUARD.**  `if (_index > maxNodeNumber) revert MerkleWrongIndex(...)`

```
    if gt(var_index, var_maxNodeNumber) {
        mstore(0, shl(224, 458764239))            -- the selector
        split_expr_2 := abi_encode_uint256_uint256(var_index, var_maxNodeNumber)
        revert(0, split_expr_2)
    }
```

The compiled form states it as one `if` on the state: when `var_index ≤ var_maxNodeNumber`
the state passes through UNCHANGED, and otherwise it reverts.  That first branch is what
the fold needs -- it is where `var_index ≤ var_maxNodeNumber` comes from, and the loop
inherits it because the guard changes nothing. -/
def A_if_4451958921457272093 (s₀ s₉ : State) : Prop :=
  let m := Clear.State.multifill ["split_expr_1"] [Fin.shiftLeft 458764239 224] s₀
  let a := s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (m["split_expr_1"]!!)⟧
  let b := Clear.State.multifill ["split_expr_1"] [Fin.shiftLeft 458764239 224] a
  ∃ s, Spec (A_abi_encode_uint256_uint256 "split_expr_2"
      (b["var_index"]!!) (b["var_maxNodeNumber"]!!)) b s ∧
    (if s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!! then s₀
      else s🇪⟦Clear.EVMState.evm_revert s.evm 0 (s["split_expr_2"]!!)⟧) = s₉

lemma if_4451958921457272093_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4451958921457272093_concrete_of_code s₀ s₉ →
  Spec A_if_4451958921457272093 s₀ s₉ := by
  unfold if_4451958921457272093_concrete_of_code A_if_4451958921457272093
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- **IN BOUNDS: THE GUARD CHANGES NOTHING.**

This is the fact the fold's accessor bounds hypothesis rests on.  `FullMerkle.updateLeaf`
establishes `_index ≤ maxNodeNumber` here, before the loop, and the loop inherits it
because on this branch the state is literally `s₀`.  Pinned by
scripts/check-source-invariants.sh so a contract edit cannot remove the guard silently. -/
lemma if_4451958921457272093_id_of_le {s₀ s₉ : State}
    (hle : s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!)
    (h : A_if_4451958921457272093 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨s, _, heq⟩ := h
  rw [if_pos hle] at heq
  exact heq.symm

/-- **OUT OF BOUNDS: the state reverts.**  The other half, so a caller that knows the call
did not revert can conclude the index was in range. -/
lemma if_4451958921457272093_revert_of_gt {s₀ s₉ : State}
    (hgt : ¬ (s₀["var_index"]!! ≤ s₀["var_maxNodeNumber"]!!))
    (h : A_if_4451958921457272093 s₀ s₉) :
    ∃ s, s₉ = s🇪⟦Clear.EVMState.evm_revert s.evm 0 (s["split_expr_2"]!!)⟧ := by
  obtain ⟨s, _, heq⟩ := h
  rw [if_neg hgt] at heq
  exact ⟨s, heq.symm⟩

end

end L2InteropCommitmentTree.Common
