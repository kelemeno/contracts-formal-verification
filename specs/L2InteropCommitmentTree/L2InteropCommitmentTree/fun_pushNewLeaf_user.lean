import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakClean
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

/-! ### The leaf counter

`pushNewLeaf` reads the count at slot 1, increments it, writes it back, and only then
rebuilds the tree.  So "the count went up by one" is really a claim about everything that
runs AFTER the write: the capacity check, the depth-extension guard, and `updateLeaf`.

`updateLeaf` is the hard one and is now settled -- it writes only keccak images, so it
cannot touch slot 1.  The two guards are not yet framed, so this is stated for the case
where both take their identity branch: a tree that is empty and not at capacity.  That is
the first-leaf path, and it is the one that exercises the whole chain. -/

/-- The entry state: the argument bound and the old count read. -/
private def entry (var_leaf : Literal) (s₀ : State) : State :=
  let f := s₀☎️⟦["var_leaf"],[var_leaf]⟧
  f⟦"_1" ↦ Clear.EVMState.sload f.evm 1⟧

private lemma entry_isOk {var_leaf : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (entry var_leaf s₀) := isOk_insert.mpr (isOk_initcall_of_isOk hok)

private lemma entry_evm {var_leaf : Literal} {s₀ : State} (hok : isOk s₀) :
    (entry var_leaf s₀).evm = s₀.evm := by
  simp only [entry, evm_insert]; exact Clear.evm_initcall hok

private lemma entry_count {var_leaf : Literal} {s₀ : State} (hok : isOk s₀) :
    (entry var_leaf s₀)["_1"]!! = Clear.EVMState.sload s₀.evm 1 := by
  simp only [entry]
  rw [lookup_insert' (isOk_initcall_of_isOk hok), Clear.evm_initcall hok]

private lemma zeroLtLowSlot : (0 : UInt256).val < Clear.KeccakInjective.lowSlotBound := by
  show (0 : ℕ) < 2 ^ 32
  norm_num

private lemma oneLtLowSlot : (1 : UInt256).val < Clear.KeccakInjective.lowSlotBound := by
  show (1 : ℕ) < 2 ^ 32
  norm_num

/-- **THE LEAF COUNT GOES UP BY ONE** -- on the first-leaf path.

Slot 1 holds the number of leaves.  `pushNewLeaf` increments it, and nothing downstream
disturbs it: the guards are identities here, and `updateLeaf` writes only keccak images,
which `fun_updateLeaf_sload_of_low_of_clean` rules out as slot 1.

The capacity path is no longer excluded: the guard's frames say it moves slots 0, 2 and 3
and ten scratch bindings, none of which is slot 1 or `_1`, so the count is tracked THROUGH
a growth rather than around it.  What replaces `hcap` is the growth path's standing
address-arithmetic assumption -- no array near `2 ^ 64` entries, none reaching `2 ^ 32` --
which is about `keccak(array) + index` wrapping onto a low slot, not about any bounds
check.

`hempty` remains, and with it the restriction to the first leaf: the depth-extension guard
is what needs the tree non-empty, and its storage frame is the one genuinely blocked on a
per-iteration length bound. -/
lemma fun_pushNewLeaf_count_of_empty
    {var_newRoot : Identifier} {var_leaf : Literal} {s₀ s₉ : State} {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (hempty : Clear.EVMState.sload s₀.evm 1 = 0)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : ∀ q : Literal, Clear.EVMState.sload s₀.evm q < 18446744073709551616)
    (hlen : ∀ q : Literal,
      (Clear.EVMState.sload s₀.evm q).val < Clear.KeccakInjective.lowSlotBound)
    (h : A_fun_pushNewLeaf var_newRoot var_leaf s₀ s₉) :
    Clear.EVMState.sload s₉.evm 1 = Clear.EVMState.sload s₀.evm 1 + 1 := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := h
  have haok := entry_isOk (var_leaf := var_leaf) hok
  have hae := entry_evm (var_leaf := var_leaf) hok
  have hac := entry_count (var_leaf := var_leaf) hok
  -- nobody ran out of fuel
  have h4nf : ¬ ❓ s₄ := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  -- each Spec starts from a WRAPPED state, so the wrappers peel on the way back
  have h2nf : ¬ ❓ s₂ := fun hoo =>
    h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃
      (by simpa only [isOutOfFuel_insert'] using hoo))
  have h1nf : ¬ ❓ s₁ := fun hoo =>
    h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
      (by simpa only [isOutOfFuel_multifill', isOutOfFuel_insert', isOutOfFuel_setEvm']
        using hoo))
  have a₁ := Spec_ok_unfold haok h1nf h₁
  have hs1 : isOk s₁ := increment_uint256_isOk h1nf a₁
  -- the counter cannot be at the sentinel, because it is zero
  have hno : (entry var_leaf s₀)["_1"]!! ≠ UInt256.lnot 0 := by
    rw [hac, hempty]
    intro hcon
    have := congrArg Fin.val hcon
    rw [lnot_zero_val] at this
    simp at this
  have hs1v : s₁["split_expr_0"]!! = (entry var_leaf s₀)["_1"]!! + 1 :=
    increment_uint256_val haok h1nf hno a₁
  have hs1_1 : s₁["_1"]!! = (entry var_leaf s₀)["_1"]!! :=
    increment_uint256_frame haok h1nf (by decide) a₁
  have hs1e : ∀ q, Clear.EVMState.sload s₁.evm q
      = Clear.EVMState.sload s₀.evm q := by
    intro q; rw [increment_uint256_sload haok h1nf a₁, hae]
  obtain ⟨hR1, hC1⟩ := increment_uint256_config haok h1nf (by rw [hae]; exact hR)
    (by rw [hae]; exact hC) a₁
  -- the write: slot 1 becomes the old count plus one
  have hacc1 : Clear.EVMState.lookupAccount s₁.evm s₁.evm.execution_env.code_owner
      = some act := by
    rw [increment_uint256_env haok h1nf a₁, hae,
      increment_uint256_account (addr := s₀.evm.execution_env.code_owner) haok h1nf a₁, hae]
    exact hacc
  have hstore : Clear.EVMState.sload
      (Clear.EVMState.sstore s₁.evm 1 (s₁["split_expr_0"]!!)) 1 = s₁["split_expr_0"]!! :=
    Clear.StorageFrame.sload_sstore_self hacc1
  -- the post-write state, and the two guard flags it decides
  set st := s₁🇪⟦Clear.EVMState.sstore s₁.evm 1 (s₁["split_expr_0"]!!)⟧ with hstdef
  have hstok : isOk st := by rw [hstdef]; simpa only [isOk_setEvm] using hs1
  have hste : st.evm = Clear.EVMState.sstore s₁.evm 1 (s₁["split_expr_0"]!!) := by
    rw [hstdef]; exact Clear.evm_setEvm_of_isOk hs1
  set lv := st⟦"_2" ↦ Clear.EVMState.sload st.evm 0⟧ with hlvdef
  have hlvok : isOk lv := by rw [hlvdef]; exact isOk_insert.mpr hstok
  set cap := Clear.State.multifill ["split_expr_1"] [Fin.shiftLeft 1 (lv["_2"]!!)] lv
    with hcapdef
  have hcapok : isOk cap := by rw [hcapdef]; exact isOk_multifill hlvok
  have hcape : cap.evm = st.evm := by
    rw [hcapdef, hlvdef, multifill_cons, multifill_nil, evm_insert, evm_insert]
  -- `_1` is the OLD count, and it is zero, so both guards fall through
  have hcap1 : cap["_1"]!! = 0 := by
    rw [hcapdef, hlvdef, multifill_cons, multifill_nil, lookup_insert_of_ne (by decide),
      lookup_insert_of_ne (by decide), hstdef, Clear.lookup_setEvm hs1, hs1_1, hac, hempty]
  have hcap2 : cap["split_expr_1"]!! = Fin.shiftLeft 1 (Clear.EVMState.sload s₀.evm 0) := by
    rw [hcapdef, multifill_cons, multifill_nil, lookup_insert' hlvok, hlvdef,
      lookup_insert' hstok, hste,
      Clear.KeccakDistinct.sload_sstore_of_ne _ (by decide), hs1e]
  -- the capacity guard may or may not fire; either way its frames carry what is needed
  have a₂ := Spec_ok_unfold hcapok h2nf h₂
  have hs2ok : isOk s₂ := L2InteropCommitmentTree.Common.if_2518866309321428816_isOk hcapok
    h2nf a₂
  -- the size assumptions, moved to the state the guard actually sees
  have hcapsl : ∀ q : Literal, q ≠ 1 →
      Clear.EVMState.sload cap.evm q = Clear.EVMState.sload s₀.evm q := by
    intro q hq
    rw [hcape, hste, Clear.KeccakDistinct.sload_sstore_of_ne _ hq, hs1e]
  have hcapfits : ∀ q : Literal, Clear.EVMState.sload cap.evm q < 18446744073709551616 := by
    intro q
    by_cases hq : q = 1
    · rw [hq, hcape, hste, hstore, hs1v, hac, hempty]; decide
    · rw [hcapsl q hq]; exact hfits q
  have hcaplen : ∀ q : Literal,
      (Clear.EVMState.sload cap.evm q).val < Clear.KeccakInjective.lowSlotBound := by
    intro q
    by_cases hq : q = 1
    · rw [hq, hcape, hste, hstore, hs1v, hac, hempty]; exact oneLtLowSlot
    · rw [hcapsl q hq]; exact hlen q
  have hRcap : Clear.KeccakLowSlot.RangeInWindow cap.evm := by
    rw [hcape, hste]; exact Clear.StorageFrame.rangeInWindow_sstore hR1
  have hCcap : Clear.KeccakLowSlot.CachedInWindow cap.evm := by
    rw [hcape, hste]; exact Clear.StorageFrame.cachedInWindow_sstore hC1
  set g2 := s₂⟦"split_expr_4" ↦ (decide (s₂["_1"]!! = 0)).toUInt256⟧ with hg2def
  have hg2ok : isOk g2 := by rw [hg2def]; exact isOk_insert.mpr hs2ok
  -- `_1` crosses the guard, so the tree is still empty when the second guard reads it
  have hs2_1 : s₂["_1"]!! = 0 := by
    rw [L2InteropCommitmentTree.Common.if_2518866309321428816_frame hcapok h2nf
      (by decide) a₂, hcap1]
  have hne2 : g2["split_expr_4"]!! ≠ 0 := by
    rw [hg2def, lookup_insert' hs2ok, hs2_1]
    decide
  have hs3 : s₃ = g2 :=
    L2InteropCommitmentTree.Common.if_8492884752647891302_id_of_ne hne2
      (Spec_ok_unfold hg2ok h3nf h₃)
  -- the fold's own frame: `updateLeaf` writes only keccak images, so not slot 1
  have hg2e : g2.evm = s₂.evm := by rw [hg2def, evm_insert]
  have he9 : s₉.evm = s₄.evm := by
    rw [heq, evm_insert, evm_setStore,
      Clear.evm_reviveJump_of_isOk (fun_updateLeaf_isOk h4nf
        (Spec_ok_unfold (by rw [hs3]; exact hg2ok) h4nf h₄))]
  -- the flag at the guard's output: walk it back through updateLeaf and the second guard
  have hcleanCap : Clear.KeccakClean.Clean s₂.evm := by
    have c3 : Clear.KeccakClean.Clean s₃.evm :=
      fun_updateLeaf_clean (by rw [hs3]; exact hg2ok) h4nf (by rw [← he9]; exact hclean)
        (Spec_ok_unfold (by rw [hs3]; exact hg2ok) h4nf h₄)
    rw [hs3, hg2e] at c3
    exact c3
  have hidx : s₃["_1"]!! = 0 := by
    rw [hs3, hg2def, lookup_insert_of_ne (by decide), hs2_1]
  have hRst : Clear.KeccakLowSlot.RangeInWindow st.evm := by
    rw [hste]; exact Clear.StorageFrame.rangeInWindow_sstore hR1
  have hCst : Clear.KeccakLowSlot.CachedInWindow st.evm := by
    rw [hste]; exact Clear.StorageFrame.cachedInWindow_sstore hC1
  have hul := fun_updateLeaf_sload_of_low_of_clean (c := 1)
    (by rw [hs3]; exact hg2ok) h4nf
    (by rw [hs3, hg2e]
        exact (L2InteropCommitmentTree.Common.if_2518866309321428816_config hcapok h2nf
          hcapfits hcaplen hRcap hCcap hcleanCap a₂).1)
    (by rw [hs3, hg2e]
        exact (L2InteropCommitmentTree.Common.if_2518866309321428816_config hcapok h2nf
          hcapfits hcaplen hRcap hCcap hcleanCap a₂).2)
    (by rw [← he9]; exact hclean)
    (by rw [hidx]; exact zeroLtLowSlot) (by exact oneLtLowSlot)
    (Spec_ok_unfold (by rw [hs3]; exact hg2ok) h4nf h₄)
  rw [he9, hul, hs3, hg2e,
    L2InteropCommitmentTree.Common.if_2518866309321428816_sload_of_ne hcapok h2nf
      (by decide) (by decide) (by decide) oneLtLowSlot hcapfits hcaplen hRcap hCcap
      hcleanCap a₂,
    hcape, hste, hstore, hs1v, hac, hempty]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
