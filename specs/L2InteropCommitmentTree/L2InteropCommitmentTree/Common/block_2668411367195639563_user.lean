import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.KeccakClean

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_5303
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2668411367195639563_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Write the leaf, and seed the fold.**

```
    _1 := add(var_self_slot, 2)                 -- the LEVELS array
    _2, _3 := storage_array_index_access_…_5278(_1)      -- element 0 = level 0's array
    _4, _5 := storage_array_index_access_…(_2, var_index) -- the leaf's slot
    update_storage_value_bytes32_to_bytes32(_4, _5, var_itemHash)
    var_currentHash := var_itemHash
```

Two facts about the generic tree's layout drop out: the LEVELS array is at
`var_self_slot + 2` (with the defaults at `+ 3`, per the sibling switch), and level 0
is the LEAF level -- element 0 of the levels array.

The leaf slot is reached through both bounds checks (levels non-empty, index within
level 0), the value written is the caller's `var_itemHash`, and the running hash the
fold starts from is that same value -- so the fold recomputes from the leaf just
written, not from anything else. -/
def A_block_2668411367195639563 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧
  ∃ s₁, Spec (A_storage_array_index_access_bytes32_dyn_ptr_5303 "_2" "_3" (a["_1"]!!)) a s₁ ∧
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "_4" "_5" (s₁["_2"]!!) (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec (A_update_storage_value_bytes32_to_bytes32
          (s₂["_4"]!!) (s₂["_5"]!!) (s₂["var_itemHash"]!!)) s₂ s₃ ∧
        s₉ = s₃⟦"var_currentHash" ↦ s₃["var_itemHash"]!!⟧

lemma block_2668411367195639563_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2668411367195639563_concrete_of_code s₀ s₉ →
  Spec A_block_2668411367195639563 s₀ s₉ := by
  unfold block_2668411367195639563_concrete_of_code A_block_2668411367195639563
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

lemma block_2668411367195639563_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2668411367195639563 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hain : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := by simpa [isOk_insert] using hok
  have hs1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn_ptr_5303_isOk h1nf (Spec_ok_unfold hain h1nf h₁)
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hs1 h2nf h₂)
  have hs3 : isOk s₃ :=
    update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃)
  simpa [isOk_insert] using hs3

lemma block_2668411367195639563_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2668411367195639563 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_2668411367195639563_isOk hok hnf h)


/-- **FRAME.**  The leaf write moves `_1`.._5` and `var_currentHash`; the index and the
bound cross it untouched, so the guard's fact reaches the fold. -/
lemma block_2668411367195639563_frame {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hv : v ∉ (["_1", "_2", "_3", "_4", "_5", "var_currentHash"] : List Identifier))
    (h : A_block_2668411367195639563 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨h1, h2, h3, h4, h5, hcur⟩ := hv
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  rw [heq] at hnf ⊢
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₂ hoo)
  have hok1 : isOk s₁ :=
    storage_array_index_access_bytes32_dyn_ptr_5303_isOk h1nf (Spec_ok_unfold haok h1nf hs₁)
  have hok2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hok1 h2nf hs₂)
  rw [lookup_insert_of_ne hcur,
    update_storage_value_bytes32_to_bytes32_frame hok2 h3nf (Spec_ok_unfold hok2 h3nf hs₃),
    storage_array_index_access_bytes32_dyn_ptr_frame hok1 h2nf h4 h5
      (Spec_ok_unfold hok1 h2nf hs₂),
    storage_array_index_access_bytes32_dyn_ptr_5303_frame haok h1nf h2 h3
      (Spec_ok_unfold haok h1nf hs₁),
    lookup_insert_of_ne h1]

/-! ### The leaf write's frames

Three callees in a row -- two address computations and one `sstore` -- so the block costs
three keccak-fuel units and touches exactly one storage slot: the one the second accessor
computed. -/

/-- Everything the three lemmas below unpack in common: the four states are `Ok` and none
of them ran out of fuel. -/
private lemma chain_ok {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    {s₁ s₂ s₃ : State}
    (hs₁ : Spec (A_storage_array_index_access_bytes32_dyn_ptr_5303 "_2" "_3"
      ((s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧)["_1"]!!))
      (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) s₁)
    (hs₂ : Spec (A_storage_array_index_access_bytes32_dyn_ptr "_4" "_5"
      (s₁["_2"]!!) (s₁["var_index"]!!)) s₁ s₂)
    (hs₃ : Spec (A_update_storage_value_bytes32_to_bytes32
      (s₂["_4"]!!) (s₂["_5"]!!) (s₂["var_itemHash"]!!)) s₂ s₃)
    (heq : s₉ = s₃⟦"var_currentHash" ↦ s₃["var_itemHash"]!!⟧) :
    (¬ ❓ s₁ ∧ ¬ ❓ s₂ ∧ ¬ ❓ s₃) ∧ (isOk s₁ ∧ isOk s₂) := by
  subst heq
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; simpa only [isOutOfFuel_insert'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hs₂ hoo)
  exact ⟨⟨h1nf, h2nf, h3nf⟩,
    storage_array_index_access_bytes32_dyn_ptr_5303_isOk h1nf (Spec_ok_unfold haok h1nf hs₁),
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold
      (storage_array_index_access_bytes32_dyn_ptr_5303_isOk h1nf
        (Spec_ok_unfold haok h1nf hs₁)) h2nf hs₂)⟩

/-- **KECCAK WINDOW.**  Two hashes and one `sstore`, none of which disturbs it. -/
lemma block_2668411367195639563_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_block_2668411367195639563 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  obtain ⟨⟨h1nf, h2nf, h3nf⟩, hok1, hok2⟩ := chain_ok hok hnf hs₁ hs₂ hs₃ heq
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have hae : (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧).evm = s₀.evm := evm_insert
  obtain ⟨hR1, hC1⟩ := storage_array_index_access_bytes32_dyn_ptr_5303_config haok h1nf
    (by rw [hae]; exact hR) (by rw [hae]; exact hC) (Spec_ok_unfold haok h1nf hs₁)
  obtain ⟨hR2, hC2⟩ := storage_array_index_access_bytes32_dyn_ptr_config hok1 h2nf hR1 hC1
    (Spec_ok_unfold hok1 h2nf hs₂)
  obtain ⟨hR3, hC3⟩ := update_storage_value_bytes32_to_bytes32_config hok2 h3nf hR2 hC2
    (Spec_ok_unfold hok2 h3nf hs₃)
  subst heq
  simpa only [evm_insert] using ⟨hR3, hC3⟩

/-- **FUEL.**  Exactly three units: a hash per accessor, and one for the `sstore`. -/
lemma block_2668411367195639563_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm (k + 3))
    (h : A_block_2668411367195639563 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  obtain ⟨⟨h1nf, h2nf, h3nf⟩, hok1, hok2⟩ := chain_ok hok hnf hs₁ hs₂ hs₃ heq
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have hae : (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧).evm = s₀.evm := evm_insert
  have hf1 : Clear.KeccakFuel.Fuel s₁.evm (k + 2) :=
    storage_array_index_access_bytes32_dyn_ptr_5303_fuel haok h1nf
      (by rw [hae]; exact hf) (Spec_ok_unfold haok h1nf hs₁)
  have hf2 : Clear.KeccakFuel.Fuel s₂.evm (k + 1) :=
    storage_array_index_access_bytes32_dyn_ptr_fuel hok1 h2nf hf1 (Spec_ok_unfold hok1 h2nf hs₂)
  have hf3 : Clear.KeccakFuel.Fuel s₃.evm k :=
    update_storage_value_bytes32_to_bytes32_fuel hok2 h3nf hf2 (Spec_ok_unfold hok2 h3nf hs₃)
  subst heq
  simpa only [evm_insert] using hf3

/-- **THE LEAF WRITE PRESERVES EVERY LOW SLOT.**

The one slot this block writes is the leaf's, and the leaf's slot is a keccak image --
so no constant-numbered slot of the tree can be the target.  The caller supplies the
keccak configuration, two units of fuel, the fact that `c` is a literal slot number, and
one genuine obligation: that `var_index` is below `2 ^ 32`.  That last one is unavoidable
here and is NOT the bounds check -- the leaf's slot is `keccak(level) + var_index`, so a
wide enough index could in principle wrap onto a constant-numbered slot.  What the caller
does not owe is the bounds check itself, since both accessors' `_slot_not_low` hold on
either branch of their guards.

This is the piece that lets `fun_updateLeaf`'s own storage frame close: the leaf write is
the only `sstore` on the path that is not already accounted for. -/
lemma block_2668411367195639563_sload_of_low {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 2)
    (hj : (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_block_2668411367195639563 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  obtain ⟨⟨h1nf, h2nf, h3nf⟩, hok1, hok2⟩ := chain_ok hok hnf hs₁ hs₂ hs₃ heq
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have hae : (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧).evm = s₀.evm := evm_insert
  -- the window and one unit of fuel reach the second accessor, which is where the
  -- written slot is minted
  obtain ⟨hR1, hC1⟩ := storage_array_index_access_bytes32_dyn_ptr_5303_config haok h1nf
    (by rw [hae]; exact hR) (by rw [hae]; exact hC) (Spec_ok_unfold haok h1nf hs₁)
  have hf1 : Clear.KeccakFuel.Fuel s₁.evm 1 :=
    storage_array_index_access_bytes32_dyn_ptr_5303_fuel haok h1nf
      (by rw [hae]; exact hf) (Spec_ok_unfold haok h1nf hs₁)
  -- the index crosses the first accessor untouched, so the caller's bound is the one
  -- the second accessor needs
  have hidx : s₁["var_index"]!! = s₀["var_index"]!! := by
    rw [storage_array_index_access_bytes32_dyn_ptr_5303_frame haok h1nf (by decide) (by decide)
      (Spec_ok_unfold haok h1nf hs₁), lookup_insert_of_ne (by decide)]
  have hne : s₂["_4"]!! ≠ c :=
    storage_array_index_access_bytes32_dyn_ptr_slot_not_low hok1 h2nf hR1 hC1 hf1
      (by rw [hidx]; exact hj) hcl (Spec_ok_unfold hok1 h2nf hs₂)
  subst heq
  rw [evm_insert,
    update_storage_value_bytes32_to_bytes32_sload_frame hok2 h3nf (Ne.symm hne)
      (Spec_ok_unfold hok2 h3nf hs₃),
    storage_array_index_access_bytes32_dyn_ptr_sload hok1 h2nf (Spec_ok_unfold hok1 h2nf hs₂),
    storage_array_index_access_bytes32_dyn_ptr_5303_sload haok h1nf
      (Spec_ok_unfold haok h1nf hs₁), hae]

/-- **THE LEAF WRITE PRESERVES EVERY LOW SLOT -- WITHOUT A FUEL BUDGET.**

Same conclusion as `_sload_of_low`, but the keccak side condition is discharged by the
collision flag on the state in hand rather than by three units of fuel counted in advance.

This is the version that composes upward.  A fuel budget has to be decided before the call,
and the enclosing function's budget would have to cover the fold as well -- `6 * k` for a
trip count `k` that only the loop's own induction reveals, and which no caller outside the
loop can name.  The flag is checked at the end, so it costs the caller nothing to state. -/
lemma block_2668411367195639563_sload_of_low_of_clean {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (hj : (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_block_2668411367195639563 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, heq⟩ := h
  obtain ⟨⟨h1nf, h2nf, h3nf⟩, hok1, hok2⟩ := chain_ok hok hnf hs₁ hs₂ hs₃ heq
  have haok : isOk (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧) := isOk_insert.mpr hok
  have hae : (s₀⟦"_1" ↦ s₀["var_self_slot"]!! + 2⟧).evm = s₀.evm := evm_insert
  obtain ⟨hR1, hC1⟩ := storage_array_index_access_bytes32_dyn_ptr_5303_config haok h1nf
    (by rw [hae]; exact hR) (by rw [hae]; exact hC) (Spec_ok_unfold haok h1nf hs₁)
  -- walk the flag back to the second accessor's output, which is where the written slot
  -- was minted: the final insert and the writer are both transparent to it
  have hclean2 : Clear.KeccakClean.Clean s₂.evm := by
    rw [heq] at hclean
    rw [evm_insert] at hclean
    exact (update_storage_value_bytes32_to_bytes32_clean hok2 h3nf
      (Spec_ok_unfold hok2 h3nf hs₃)).mp hclean
  have hidx : s₁["var_index"]!! = s₀["var_index"]!! := by
    rw [storage_array_index_access_bytes32_dyn_ptr_5303_frame haok h1nf (by decide) (by decide)
      (Spec_ok_unfold haok h1nf hs₁), lookup_insert_of_ne (by decide)]
  have hne : s₂["_4"]!! ≠ c :=
    storage_array_index_access_bytes32_dyn_ptr_slot_not_low_of_clean hok1 h2nf hR1 hC1
      hclean2 (by rw [hidx]; exact hj) hcl (Spec_ok_unfold hok1 h2nf hs₂)
  subst heq
  rw [evm_insert,
    update_storage_value_bytes32_to_bytes32_sload_frame hok2 h3nf (Ne.symm hne)
      (Spec_ok_unfold hok2 h3nf hs₃),
    storage_array_index_access_bytes32_dyn_ptr_sload hok1 h2nf (Spec_ok_unfold hok1 h2nf hs₂),
    storage_array_index_access_bytes32_dyn_ptr_5303_sload haok h1nf
      (Spec_ok_unfold haok h1nf hs₁), hae]

end

end L2InteropCommitmentTree.Common
