import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2960513488629726830
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_4511405458545096882
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_5278
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1667634760212566376
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4843491680166179088
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_updateLeaf_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`fun_updateLeaf(self, index, itemHash)` — write a leaf and recompute the root.**

The deployed leaf update, and the first spec in this corpus that ties the tree's
storage layout, its bound checks and its Merkle fold into one statement:

1. `maxNodeNumber := checked_sub_uint256(sload(self + 1))` — the leaf count minus one,
   through the CHECKED decrement, so an empty tree reverts rather than wrapping;
2. `if_2960513488629726830` — reject `index > maxNodeNumber` with the named error
   `MerkleWrongIndex(index, maxNodeNumber)`;
3. `block_2668411367195639563` — write `itemHash` into level 0 at `index`, and seed the
   running hash with that same value;
4. zero the level counter, then run the fold loop.

The loop enters this spec through its POSTCONDITION, `AFor_for_5363593723278629209` --
which is why giving that loop a real `AFor` mattered: a caller of `fun_updateLeaf` sees
"the fold ran until the level index reached the stored level count", not `True`.

The returned `var_` is the running hash after the fold, i.e. the recomputed root. -/
def A_fun_updateLeaf (var_ : Identifier) (var_self_slot var_index var_itemHash : Literal)
    (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
    var_itemHash]⟧
  let a := f⟦"split_expr_0" ↦ f["var_self_slot"]!! + 1⟧
  let b := a⟦"split_expr_1" ↦ Clear.EVMState.sload f.evm (a["split_expr_0"]!!)⟧
  ∃ s₁, Spec (A_checked_sub_uint256 "var_maxNodeNumber" (b["split_expr_1"]!!)) b s₁ ∧
    ∃ s₂, Spec L2InteropCommitmentTree.Common.A_if_2960513488629726830 s₁ s₂ ∧
      ∃ s₃, Spec L2InteropCommitmentTree.Common.A_block_2668411367195639563 s₂ s₃ ∧
        ∃ s₄, Spec L2InteropCommitmentTree.Common.A_block_1667634760212566376 s₃ s₄ ∧
          ∃ s₅, Spec L2InteropCommitmentTree.Common.AFor_for_5363593723278629209 s₄ s₅ ∧
            (let r := s₅⟦"var_" ↦ s₅["var_currentHash"]!!⟧
             s₉ = 🧟r🏪⟦s₀⟧⟦var_ ↦ r["var_"]!!⟧)

lemma fun_updateLeaf_abs_of_concrete {s₀ s₉ : State} {var_ var_self_slot var_index var_itemHash} :
  Spec (fun_updateLeaf_concrete_of_code.1 var_ var_self_slot var_index var_itemHash) s₀ s₉ →
  Spec (A_fun_updateLeaf var_ var_self_slot var_index var_itemHash) s₀ s₉ := by
  unfold fun_updateLeaf_concrete_of_code A_fun_updateLeaf
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma fun_updateLeaf_isOk {var_ : Identifier} {var_self_slot var_index var_itemHash : Literal}
    {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_updateLeaf var_ var_self_slot var_index var_itemHash s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, s₄, _, s₅, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma fun_updateLeaf_not_break {var_ : Identifier} {var_self_slot var_index var_itemHash : Literal}
    {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_updateLeaf var_ var_self_slot var_index var_itemHash s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (fun_updateLeaf_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
