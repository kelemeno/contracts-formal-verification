import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.increment_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1084122831851539501
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_uncheckedInc
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.allocate_memory
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_array_bytes32_to_array_array_bytes32_dyn_storage_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3948411532618903895
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_updateLeaf

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_pushNewLeaf_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`fun_pushNewLeaf(leaf)` — insert a leaf and return the new root.**

The deployed insertion path, and the top of the tree chain:

```
    _1 := sload(1)                        -- the leaf count, i.e. the NEW leaf's index
    split_expr_0 := increment_uint256(_1) -- CHECKED increment
    sstore(1, split_expr_0)               -- leaf count += 1
    _2 := sload(0)                        -- level count
    split_expr_1 := shl(_2, 1)            -- capacity = 1 << levels
    if eq(_1, split_expr_1) { grow a level }          -- if_2518866309321428816
    if iszero(_1) { copy up }                        -- if_8492884752647891302
    var_newRoot := fun_updateLeaf(0, _1, leaf)
```

Three things this makes explicit:

- the index the leaf is written at is the count read BEFORE the increment, so leaves are
  appended and never overwrite each other;
- the count is bumped through the CHECKED increment, so the leaf index cannot wrap (the
  LEVEL count, by contrast, uses the unchecked one -- see `fun_uncheckedInc`);
- growth happens BEFORE the write, so `fun_updateLeaf`'s own bound check
  (`index ≤ maxNodeNumber`, else `MerkleWrongIndex`) is evaluated against the already
  grown tree.

Below this sit 58 specs: the fold with its parity and right-edge cases, the empty-subtree
default chain, the bounds-checked storage accessors, the array push with its stale-reuse
zero-fill, and the memory allocator. -/
def A_fun_pushNewLeaf (var_newRoot : Identifier) (var_leaf : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["var_leaf"],[var_leaf]⟧
  let a := f⟦"_1" ↦ Clear.EVMState.sload f.evm 1⟧
  ∃ s₁, Spec (A_increment_uint256 "split_expr_0" (a["_1"]!!)) a s₁ ∧
    (let st := s₁🇪⟦Clear.EVMState.sstore s₁.evm 1 (s₁["split_expr_0"]!!)⟧
     let lv := st⟦"_2" ↦ Clear.EVMState.sload st.evm 0⟧
     let cap := Clear.State.multifill ["split_expr_1"] [Fin.shiftLeft 1 (lv["_2"]!!)] lv
     ∃ s₂, Spec L2InteropCommitmentTree.Common.A_if_2518866309321428816 cap s₂ ∧
       ∃ s₃, Spec L2InteropCommitmentTree.Common.A_if_8492884752647891302
           (s₂⟦"split_expr_4" ↦ (decide (s₂["_1"]!! = 0)).toUInt256⟧) s₃ ∧
         ∃ s₄, Spec (A_fun_updateLeaf "var_newRoot" 0 (s₃["_1"]!!) (s₃["var_leaf"]!!)) s₃ s₄ ∧
           s₉ = 🧟s₄🏪⟦s₀⟧⟦var_newRoot ↦ s₄["var_newRoot"]!!⟧)

lemma fun_pushNewLeaf_abs_of_concrete {s₀ s₉ : State} {var_newRoot var_leaf} :
  Spec (fun_pushNewLeaf_concrete_of_code.1 var_newRoot var_leaf) s₀ s₉ →
  Spec (A_fun_pushNewLeaf var_newRoot var_leaf) s₀ s₉ := by
  unfold fun_pushNewLeaf_concrete_of_code A_fun_pushNewLeaf
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma fun_pushNewLeaf_isOk {var_newRoot : Identifier} {var_leaf : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_fun_pushNewLeaf var_newRoot var_leaf s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, s₄, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma fun_pushNewLeaf_not_break {var_newRoot : Identifier} {var_leaf : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_fun_pushNewLeaf var_newRoot var_leaf s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (fun_pushNewLeaf_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
