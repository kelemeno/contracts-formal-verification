import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4451958921457272093
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1492471849597063814
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_5278
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5752024616743232143
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4939860823883042599
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_updateLeaf_5202_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`FullMerkle.updateLeaf`, the deployed function.**

```
    split_expr_0      := sload(1)                       -- _leafNumber
    var_maxNodeNumber := checked_sub_uint256(...)       -- _leafNumber - 1
    if gt(var_index, var_maxNodeNumber) { revert MerkleWrongIndex }
    _3, _4 := storage_array_index_access(_nodes[0], var_index)
    update_storage_value(_3, _4, var_itemHash)          -- write the leaf
    var_currentHash := var_itemHash ; var_i := 0
    for { } 1 { var_i := add(var_i,1) } { … }           -- the fold
```

Converted from an ALIAS because the entry guard lives HERE, not in the loop: the fold's
accessor bounds hypothesis is `var_index ≤ var_maxNodeNumber`, and
`if_4451958921457272093` is what establishes it.  While this spec was an alias the guard
was invisible, so the loop's `hlt` had nowhere to come from.  See SECURITY_VERIFICATION.md
Part H. -/
def A_fun_updateLeaf_5202 (var : Identifier) (var_index var_itemHash : Literal)
    (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["var_index", "var_itemHash"],[var_index, var_itemHash]⟧
  let g := f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm 1⟧
  ∃ s₁, Spec (A_checked_sub_uint256 "var_maxNodeNumber" (g["split_expr_0"]!!)) g s₁ ∧
    ∃ s₂, Spec L2InteropCommitmentTree.Common.A_if_4451958921457272093 s₁ s₂ ∧
      ∃ s₃, Spec L2InteropCommitmentTree.Common.A_block_1492471849597063814 s₂ s₃ ∧
        ∃ s₄, Spec L2InteropCommitmentTree.Common.A_block_5752024616743232143 s₃ s₄ ∧
          ∃ s₅, Spec L2InteropCommitmentTree.Common.AFor_for_4939860823883042599 s₄ s₅ ∧
            s₉ = 🧟(s₅⟦"var" ↦ s₅["var_currentHash"]!!⟧)🏪⟦s₀⟧⟦var ↦
              (s₅⟦"var" ↦ s₅["var_currentHash"]!!⟧)["var"]!!⟧

lemma fun_updateLeaf_5202_abs_of_concrete {s₀ s₉ : State} {var var_index var_itemHash} :
  Spec (fun_updateLeaf_5202_concrete_of_code.1 var var_index var_itemHash) s₀ s₉ →
  Spec (A_fun_updateLeaf_5202 var var_index var_itemHash) s₀ s₉ := by
  unfold fun_updateLeaf_5202_concrete_of_code A_fun_updateLeaf_5202
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩
end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
