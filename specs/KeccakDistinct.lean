import Clear.EVMState

/-!
# Keccak slot-distinctness and sstore non-aliasing

Framework infrastructure for storage-effect proofs in the Clear model.

The headline use case: a proof shows a value is written at some keccak-derived
storage slot mid-execution, and we need to know that this write *survives* later
`sstore`s to *different* slots, so a "mid-execution write" proof can be upgraded
to an "end-of-call write" proof.

Two ingredients are provided here:

* `sload_sstore_of_ne` — `sstore` at slot `b` leaves `sload` at any *other* slot
  `a` unchanged. This is the workhorse: whenever the two slots are syntactically
  distinct `UInt256`s it discharges the "later write does not clobber my slot"
  obligation directly from the model definitions.

* keccak non-aliasing (`keccak256_fresh_*` and `keccak256_distinct_sequential`) —
  the freshness/`used_range` mechanism guarantees that a *fresh* `keccak256` call
  returns a slot that is not in the current `used_range`, and that this slot is
  recorded into the new state's `used_range`. Chaining these gives: two
  back-to-back keccak calls whose preimages are both fresh yield *distinct* slots.

This file is ported (axiom-free) to the main repo's toolchain (Lean 4.9.1).

See the note at the bottom of this file for what full keccak injectivity
(arbitrary, non-sequential calls) would additionally require.
-/

namespace Clear.KeccakDistinct

open Clear EVMState

/-! ## sstore non-aliasing: a write at slot `b` preserves reads at any other slot `a`. -/

/-- `Account.updateStorage` at slot `b` preserves `lookupStorage` at any other slot `a`. -/
theorem lookupStorage_updateStorage_of_ne
    (act : Account) {a b v : UInt256} (h : a ≠ b) :
    (act.updateStorage b v).lookupStorage a = act.lookupStorage a := by
  unfold Account.updateStorage Account.lookupStorage
  by_cases hv : v == 0
  · -- erase branch
    rw [if_pos hv]
    rw [Finmap.lookup_erase_ne h]
  · -- insert branch
    rw [if_neg hv]
    rw [Finmap.lookup_insert_of_ne _ h]

/-- The slot a write was made to: `updateStorage` at `b` sets `lookupStorage b` to
the written value (when the value is non-zero) or to `0` (when it is `0`, since the
model erases zero entries). The combined statement is just that re-reading the
written slot returns the canonical reading of `v`. -/
theorem lookupStorage_updateStorage_self
    (act : Account) (b v : UInt256) :
    (act.updateStorage b v).lookupStorage b = (if v == 0 then 0 else v) := by
  unfold Account.updateStorage Account.lookupStorage
  by_cases hv : v == 0
  · rw [if_pos hv, if_pos hv, Finmap.lookup_erase]
  · rw [if_neg hv, if_neg hv, Finmap.lookup_insert]

/-- **Main non-aliasing lemma.** An `sstore` at slot `b` leaves `sload` at any
other slot `a` unchanged. This is exactly what lets a storage-effect proof carry a
write at one slot through later `sstore`s to syntactically-distinct slots. -/
theorem sload_sstore_of_ne
    (σ : EVMState) {a b v : UInt256} (h : a ≠ b) :
    (σ.sstore b v).sload a = σ.sload a := by
  unfold EVMState.sstore EVMState.sload
  -- `sstore`/`sload` both read the `code_owner` account.
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none =>
    -- No account: `sstore` is the identity, `sload` returns 0 either way.
    simp only [hacc]
  | some act =>
    simp only [hacc]
    -- After `sstore` we read the *updated* account at `code_owner`.
    -- `lookupAccount` on the post-state hits the freshly-inserted account.
    -- The `used_range` override does not touch `account_map`, so the lookup
    -- reduces to `Finmap.lookup_insert`.
    unfold EVMState.lookupAccount EVMState.updateAccount
    simp only [Finmap.lookup_insert]
    -- Reduce to the account-level non-aliasing lemma.
    exact lookupStorage_updateStorage_of_ne act h

/-! ## keccak non-aliasing via the freshness / `used_range` mechanism. -/

/-- A *fresh* `keccak256` call (preimage not yet in `keccak_map`, and the
unused part of `keccak_range` non-empty) succeeds and returns a slot that is
**not** in the current `used_range`. This is the core freshness guarantee. -/
theorem keccak256_fresh_not_mem_used
    (σ : EVMState) (p n r : UInt256) (σ' : EVMState)
    (hres : σ.keccak256 p n = some (r, σ')) :
    let interval := mkInterval σ.machine_state p n
    Finmap.lookup interval σ.keccak_map = none →
    r ∉ σ.used_range := by
  intro interval hmap
  -- Unfold `keccak256` and drive through the `match`.
  unfold EVMState.keccak256 at hres
  simp only [hmap] at hres
  -- Now the result is the partition branch.
  -- `r` is the head of `(keccak_range.partition (· ∈ used_range)).2`.
  cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
  | mk used unused =>
    cases unused with
    | nil =>
      simp only [hpart] at hres
    | cons hd tl =>
      simp only [hpart] at hres
      -- `hres : some (hd, ...) = some (r, σ')`
      have hr : r = hd := by
        injection hres with hres1
        injection hres1 with h1 _
        exact h1.symm
      subst hr
      -- `r = hd ∈ unused = (partition ...).2`, and elements of `.2` fail the predicate.
      have hmem : r ∈ (σ.keccak_range.partition (fun x => x ∈ σ.used_range)).2 := by
        rw [hpart]; exact List.mem_cons_self _ _
      rw [List.partition_eq_filter_filter] at hmem
      -- membership in `filter (not ∘ p)` gives `¬ p r`.
      rw [List.mem_filter] at hmem
      have hnp : (decide (r ∈ σ.used_range)) = false := by
        have := hmem.2
        simpa using this
      simpa using hnp

/-- A *fresh* `keccak256` call records its returned slot into the new state's
`used_range`. Concretely the new `used_range` is `{r} ∪ σ.used_range`, so in
particular `r` is a member. -/
theorem keccak256_fresh_mem_used'
    (σ : EVMState) (p n r : UInt256) (σ' : EVMState)
    (hres : σ.keccak256 p n = some (r, σ')) :
    let interval := mkInterval σ.machine_state p n
    Finmap.lookup interval σ.keccak_map = none →
    r ∈ σ'.used_range := by
  intro interval hmap
  unfold EVMState.keccak256 at hres
  simp only [hmap] at hres
  cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
  | mk used unused =>
    cases unused with
    | nil =>
      simp only [hpart] at hres
    | cons hd tl =>
      simp only [hpart] at hres
      -- Recover both `r = hd` and the shape of `σ'`.
      injection hres with hres1
      injection hres1 with hr hσ'
      subst hr
      subst hσ'
      -- `σ'.used_range = {hd} ∪ σ.used_range`.
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

/-- **Sequential keccak distinctness.** Two back-to-back `keccak256` calls whose
preimages are both *fresh* (not in the respective `keccak_map`) return **distinct**
slots. Concretely: if `keccak256 p₁ n₁` on `σ` yields `(r₁, σ₁)` freshly, and
`keccak256 p₂ n₂` on `σ₁` yields `(r₂, σ₂)` freshly, then `r₁ ≠ r₂`.

This is the form that storage-effect proofs actually need when a function hashes
two different keys in sequence and writes to both: the two derived slots provably
do not alias, so the two writes are independent (and combine with
`sload_sstore_of_ne` above). -/
theorem keccak256_distinct_sequential
    (σ σ₁ σ₂ : EVMState) (p₁ n₁ p₂ n₂ r₁ r₂ : UInt256)
    (hres₁ : σ.keccak256 p₁ n₁ = some (r₁, σ₁))
    (hfresh₁ : Finmap.lookup (mkInterval σ.machine_state p₁ n₁) σ.keccak_map = none)
    (hres₂ : σ₁.keccak256 p₂ n₂ = some (r₂, σ₂))
    (hfresh₂ : Finmap.lookup (mkInterval σ₁.machine_state p₂ n₂) σ₁.keccak_map = none) :
    r₁ ≠ r₂ := by
  -- `r₁` is recorded into `σ₁.used_range`.
  have h₁ : r₁ ∈ σ₁.used_range :=
    keccak256_fresh_mem_used' σ p₁ n₁ r₁ σ₁ hres₁ hfresh₁
  -- `r₂` is fresh w.r.t. `σ₁.used_range`, hence not in it.
  have h₂ : r₂ ∉ σ₁.used_range :=
    keccak256_fresh_not_mem_used σ₁ p₂ n₂ r₂ σ₂ hres₂ hfresh₂
  intro hcontra
  subst hcontra
  exact h₂ h₁

end Clear.KeccakDistinct
