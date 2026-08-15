import Clear.ReasoningPrinciple
import specs.StateOk
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.KeccakFuel

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

/-- **`updateLeaf` NEVER WRITES A CONSTANT-NUMBERED SLOT.**

The tree's own bookkeeping -- the level count, the node counter, the defaults pointer --
lives at slots named by literals off `var_self_slot`.  This says an update cannot disturb
any of them: everything `updateLeaf` writes is a keccak image, from the leaf itself through
every internal node the fold recomputes.

The caller owes four things, and none of them is a step count:

  * `hR`/`hC`   the keccak window, the standing configuration hypothesis;
  * `hclean`    no hash on the path exhausted the pool -- read off the FINAL state, so the
                caller checks it rather than budgeting for it;
  * `hj`        the leaf index is below `2 ^ 32`.  This is a real assumption about the
                argument and not a consequence of the bounds check: the leaf's slot is
                `keccak(level) + var_index`, so a wide enough index could in principle wrap
                onto a low slot.  Any real tree satisfies it;
  * `hcl`       `c` is one of those literal slot numbers.

What the caller does NOT owe is the fold's trip count.  Getting to that was the point of
the clean-flag layer: the budgeted form of this statement would have had to name `6 * k`
for a `k` only the loop's induction ever learns. -/
lemma fun_updateLeaf_sload_of_low_of_clean
    {var_ : Identifier} {var_self_slot var_index var_itemHash c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (hj : var_index.val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_fun_updateLeaf var_ var_self_slot var_index var_itemHash s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  -- the entry state: an initcall and two scratch bindings, so the evm is the caller's
  set b := ((s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
      var_itemHash]⟧)⟦"split_expr_0" ↦
        (s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
          var_itemHash]⟧)["var_self_slot"]!! + 1⟧)⟦"split_expr_1" ↦
      Clear.EVMState.sload (s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],
        [var_self_slot, var_index, var_itemHash]⟧).evm
        (((s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
          var_itemHash]⟧)⟦"split_expr_0" ↦
            (s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
              var_itemHash]⟧)["var_self_slot"]!! + 1⟧)["split_expr_0"]!!)⟧ with hbdef
  have hbok : isOk b := by
    rw [hbdef]; exact isOk_insert.mpr (isOk_insert.mpr (isOk_initcall_of_isOk hok))
  have hbe : b.evm = s₀.evm := by
    rw [hbdef]; simp only [evm_insert]; exact Clear.evm_initcall hok
  have hbi : b["var_index"]!! = var_index := by
    rw [hbdef, lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    exact Clear.lookup_initcall_snd3 (by decide) hok
  -- nobody ran out of fuel
  have h5nf : ¬ ❓ s₅ := by
    intro hoo
    apply hnf
    rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have a₁ := Spec_ok_unfold hbok h1nf h₁
  have hs1 : isOk s₁ := checked_sub_uint256_isOk hbok h1nf a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := L2InteropCommitmentTree.Common.if_2960513488629726830_isOk hs1 h2nf a₂
  have a₃ := Spec_ok_unfold hs2 h3nf h₃
  have hs3 : isOk s₃ :=
    L2InteropCommitmentTree.Common.block_2668411367195639563_isOk hs2 h3nf a₃
  have a₄ := Spec_ok_unfold hs3 h4nf h₄
  have hs4 : isOk s₄ :=
    L2InteropCommitmentTree.Common.block_1667634760212566376_isOk hs3 a₄
  have a₅ := Spec_ok_unfold hs4 h5nf h₅
  have hs5 : isOk s₅ := a₅.2.2.1
  -- the final `setStore` keeps the fold's evm, so the caller's flag is the fold's flag
  have he9 : s₉.evm = s₅.evm := by
    rw [heq, evm_insert, evm_setStore, Clear.evm_reviveJump_of_isOk (isOk_insert.mpr hs5),
      evm_insert]
  rw [he9] at hclean
  -- STEP 1: the flag walks back to every point that needs it
  have c4 : Clear.KeccakClean.Clean s₄.evm := a₅.2.2.2.1 hs5 hclean
  have c3 : Clear.KeccakClean.Clean s₃.evm :=
    (L2InteropCommitmentTree.Common.block_1667634760212566376_clean a₄).mp c4
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    L2InteropCommitmentTree.Common.block_2668411367195639563_clean hs2 h3nf c3 a₃
  -- STEP 2: the window travels forward to the fold
  obtain ⟨hR1, hC1⟩ := checked_sub_uint256_config hbok h1nf (by rw [hbe]; exact hR)
    (by rw [hbe]; exact hC) a₁
  obtain ⟨hR2, hC2⟩ :=
    L2InteropCommitmentTree.Common.if_2960513488629726830_config hs1 h2nf hR1 hC1 a₂
  obtain ⟨hR3, hC3⟩ :=
    L2InteropCommitmentTree.Common.block_2668411367195639563_config hs2 h3nf hR2 hC2 a₃
  obtain ⟨hR4, hC4⟩ :=
    L2InteropCommitmentTree.Common.block_1667634760212566376_config hR3 hC3 a₄
  -- STEP 3: the index reaches the leaf write and the fold with its bound intact
  have hi1 : s₁["var_index"]!! = b["var_index"]!! :=
    checked_sub_uint256_frame hbok h1nf (by decide) a₁
  have hi2 : s₂["var_index"]!! = s₁["var_index"]!! :=
    L2InteropCommitmentTree.Common.if_2960513488629726830_frame hs1 h2nf (by decide)
      (by decide) a₂
  have hi3 : s₃["var_index"]!! = s₂["var_index"]!! :=
    L2InteropCommitmentTree.Common.block_2668411367195639563_frame hs2 h3nf (by decide) a₃
  have hi4 : s₄["var_index"]!! = s₃["var_index"]!! :=
    L2InteropCommitmentTree.Common.block_1667634760212566376_frame (by decide) a₄
  have hj2 : (s₂["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound := by
    rw [hi2, hi1, hbi]; exact hj
  have hj4 : (s₄["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound := by
    rw [hi4, hi3]; exact hj2
  -- STEP 4: nothing on the path touches slot `c`
  rw [he9, a₅.2.2.2.2.1 hs5 hclean hR4 hC4 hj4 c hcl,
    L2InteropCommitmentTree.Common.block_1667634760212566376_sload a₄,
    L2InteropCommitmentTree.Common.block_2668411367195639563_sload_of_low_of_clean hs2 h3nf
      hR2 hC2 c3 hj2 hcl a₃,
    L2InteropCommitmentTree.Common.if_2960513488629726830_sload hs1 h2nf a₂,
    checked_sub_uint256_sload hbok h1nf a₁, hbe]

/-- **CLEAN FLAG, BACKWARDS, ACROSS THE WHOLE UPDATE.**

Companion to `_sload_of_low_of_clean`: that one CONSUMES the flag, this one carries it
back to the caller, which is what a caller needs in order to establish the flag at
whatever earlier point its own frames are stated. -/
lemma fun_updateLeaf_clean
    {var_ : Identifier} {var_self_slot var_index var_itemHash : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_fun_updateLeaf var_ var_self_slot var_index var_itemHash s₀ s₉) :
    Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  set b := ((s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
      var_itemHash]⟧)⟦"split_expr_0" ↦
        (s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
          var_itemHash]⟧)["var_self_slot"]!! + 1⟧)⟦"split_expr_1" ↦
      Clear.EVMState.sload (s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],
        [var_self_slot, var_index, var_itemHash]⟧).evm
        (((s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
          var_itemHash]⟧)⟦"split_expr_0" ↦
            (s₀☎️⟦["var_self_slot", "var_index", "var_itemHash"],[var_self_slot, var_index,
              var_itemHash]⟧)["var_self_slot"]!! + 1⟧)["split_expr_0"]!!)⟧ with hbdef
  have hbok : isOk b := by
    rw [hbdef]; exact isOk_insert.mpr (isOk_insert.mpr (isOk_initcall_of_isOk hok))
  have hbe : b.evm = s₀.evm := by
    rw [hbdef]; simp only [evm_insert]; exact Clear.evm_initcall hok
  have h5nf : ¬ ❓ s₅ := by
    intro hoo
    apply hnf
    rw [heq]
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have a₁ := Spec_ok_unfold hbok h1nf h₁
  have hs1 : isOk s₁ := checked_sub_uint256_isOk hbok h1nf a₁
  have a₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := L2InteropCommitmentTree.Common.if_2960513488629726830_isOk hs1 h2nf a₂
  have a₃ := Spec_ok_unfold hs2 h3nf h₃
  have hs3 : isOk s₃ :=
    L2InteropCommitmentTree.Common.block_2668411367195639563_isOk hs2 h3nf a₃
  have a₄ := Spec_ok_unfold hs3 h4nf h₄
  have hs4 : isOk s₄ :=
    L2InteropCommitmentTree.Common.block_1667634760212566376_isOk hs3 a₄
  have a₅ := Spec_ok_unfold hs4 h5nf h₅
  have hs5 : isOk s₅ := a₅.2.2.1
  have he9 : s₉.evm = s₅.evm := by
    rw [heq, evm_insert, evm_setStore, Clear.evm_reviveJump_of_isOk (isOk_insert.mpr hs5),
      evm_insert]
  rw [he9] at hclean
  have c4 : Clear.KeccakClean.Clean s₄.evm := a₅.2.2.2.1 hs5 hclean
  have c3 : Clear.KeccakClean.Clean s₃.evm :=
    (L2InteropCommitmentTree.Common.block_1667634760212566376_clean a₄).mp c4
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    L2InteropCommitmentTree.Common.block_2668411367195639563_clean hs2 h3nf c3 a₃
  have c1 : Clear.KeccakClean.Clean s₁.evm :=
    (L2InteropCommitmentTree.Common.if_2960513488629726830_clean hs1 h2nf a₂).mp c2
  have cb := (checked_sub_uint256_clean hbok h1nf a₁).mp c1
  rw [hbe] at cb
  exact cb

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
