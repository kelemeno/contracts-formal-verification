import specs.KeccakFresh
import specs.KeccakInjective

/-
  KECCAK NEVER HITS A LOW SLOT — DERIVED FROM THE MODEL'S RANGE, NOT AXIOMATIZED.

  `Clear.KeccakInjective` posits `keccak256_ne_lowSlot` as an AXIOM: a keccak call never returns a reserved/small
  slot (`< 2^32`).  Its justification is cryptographic — real keccak output is a near-uniform 256-bit value, so a
  collision below `2^32` is negligible.

  But in Clear's model a keccak result is not a hash at all: it is drawn from `keccak_range`, the pool of fresh
  slots.  So the property is not about keccak — it is about how the pool is CONFIGURED, and it can be PROVED from
  that configuration rather than assumed:

    * `NoLowInRange` — the fresh-slot pool contains no low slot;
    * `NoLowCached`  — no cached value is a low slot;

  and the second is preserved because every value ever cached was drawn from the pool.  Given both, a keccak step
  cannot return a low slot.

  This is strictly better than the axiom: it makes the assumption a checkable property of the model's
  instantiation instead of an idealization, and it is honest about where the real idealization lives — in the
  freshness mechanism itself, not in an extra hypothesis about hash values.

  Axiom-free (in particular it does NOT depend on the `KeccakInjective` axioms, which this file only imports for
  `lowSlotBound`).
-/

namespace Clear.KeccakLowSlot

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakInjective EVMState

/-- The fresh-slot pool contains no low slot. -/
def NoLowInRange (σ : EVMState) : Prop :=
  ∀ x ∈ σ.keccak_range, lowSlotBound ≤ x.val

/-- No value in the keccak cache is a low slot. -/
def NoLowCached (σ : EVMState) : Prop :=
  ∀ (I : List UInt256) (v : UInt256),
    Finmap.lookup I σ.keccak_map = some v → lowSlotBound ≤ v.val

/-- The pool only shrinks, so the configuration survives a hash step. -/
theorem noLowInRange_keccakOut {σ : EVMState} {p n : UInt256}
    (hR : NoLowInRange σ) : NoLowInRange (keccakOut σ p n).2 := by
  unfold keccakOut EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some v => simpa [hl] using hR
  | none =>
    cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
    | mk used unused =>
      cases unused with
      | nil => simp only [hl, hpart]; exact hR
      | cons hd tl =>
        simp only [hl, hpart]
        intro x hx
        -- `tl` is a tail of a filter of the original range
        have hsub : tl ⊆ σ.keccak_range := by
          intro y hy
          rw [List.partition_eq_filter_filter] at hpart
          have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
            ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
          have : y ∈ σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) := by
            rw [← h2]; exact List.mem_cons_of_mem _ hy
          exact List.mem_of_mem_filter this
        exact hR x (hsub hx)

/-- **PRESERVATION.**  Every value entering the cache is drawn from the pool, so if the pool has no low slot the
cache never acquires one. -/
theorem noLowCached_keccakOut {σ : EVMState} {p n : UInt256}
    (hR : NoLowInRange σ) (hC : NoLowCached σ) : NoLowCached (keccakOut σ p n).2 := by
  unfold keccakOut EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some v => simpa [hl] using hC
  | none =>
    cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
    | mk used unused =>
      cases unused with
      | nil => simp only [hl, hpart]; exact hC
      | cons hd tl =>
        simp only [hl, hpart]
        have hhd : hd ∈ σ.keccak_range := by
          rw [List.partition_eq_filter_filter] at hpart
          have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
            ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
          have : hd ∈ σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) := by
            rw [← h2]; exact List.mem_cons_self _ _
          exact List.mem_of_mem_filter this
        intro I v hv
        by_cases hI : I = mkInterval σ.machine_state p n
        · subst hI
          rw [Finmap.lookup_insert] at hv
          rw [← Option.some.inj hv]
          exact hR hd hhd
        · rw [Finmap.lookup_insert_of_ne _ hI] at hv
          exact hC I v hv

/-- **KECCAK NEVER RETURNS A LOW SLOT — PROVED.**  On a hit the value was cached and so is not low; on a miss it is
drawn from the pool and so is not low.  The non-exhaustion hypothesis is necessary: an exhausted pool makes the
model return `0`, which IS a low slot, so the statement would be false without it. -/
theorem keccakOut_ne_lowSlot {σ : EVMState} {p n : UInt256}
    (hR : NoLowInRange σ) (hC : NoLowCached σ)
    (hfuel : (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ [])
    (c : UInt256) (hc : c.val < lowSlotBound) :
    (keccakOut σ p n).1 ≠ c := by
  intro he
  have hlow : lowSlotBound ≤ (keccakOut σ p n).1.val := by
    unfold keccakOut EVMState.keccak256
    cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
    | some v => simpa [hl] using hC _ v hl
    | none =>
      cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
      | mk used unused =>
        cases unused with
        | nil => rw [hpart] at hfuel; exact absurd rfl hfuel
        | cons hd tl =>
          simp only [hl, hpart]
          refine hR hd ?_
          rw [List.partition_eq_filter_filter] at hpart
          have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
            ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
          have : hd ∈ σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) := by
            rw [← h2]; exact List.mem_cons_self _ _
          exact List.mem_of_mem_filter this
  rw [he] at hlow
  omega

/-- `mstore` preserves both, and hence an accessor step does. -/
theorem noLow_accOut {σ : EVMState} {key base : UInt256}
    (hR : NoLowInRange σ) (hC : NoLowCached σ) :
    NoLowInRange (accOut σ key base).2 ∧ NoLowCached (accOut σ key base).2 :=
  ⟨noLowInRange_keccakOut hR, noLowCached_keccakOut hR hC⟩

/-! ## DROP-IN SHAPE

The axiom is stated on `keccak256 … = some (r, σ')` rather than on `keccakOut`.  Restating the derived version the
same way is strictly better than the `keccakOut` form above: a successful call is evidence that the pool was NOT
exhausted, so the non-exhaustion hypothesis disappears entirely.  What remains is exactly the pool configuration. -/

/-- **DROP-IN FOR `KeccakInjective.keccak256_ne_lowSlot`.**  A successful keccak call never returns a low slot, given
the pool holds none and the cache holds none.

No non-exhaustion hypothesis is needed here: `h` witnesses that the call succeeded, which already rules out the
exhausted case. -/
theorem keccak256_ne_lowSlot_of_config {σ σ' : EVMState} {p n r : UInt256} (c : UInt256)
    (hR : NoLowInRange σ) (hC : NoLowCached σ)
    (h : σ.keccak256 p n = some (r, σ')) (hc : c.val < lowSlotBound) : r ≠ c := by
  -- the successful call IS the `keccakOut` step, so the post-state config transfers
  have hko : keccakOut σ p n = (r, σ') := by unfold keccakOut; rw [h]
  have hpost : NoLowCached σ' := by
    have hn := noLowCached_keccakOut (σ := σ) (p := p) (n := n) hR hC
    rw [hko] at hn
    exact hn
  -- and the call caches its own result in that state
  have hcached : Finmap.lookup (mkInterval σ.machine_state p n) σ'.keccak_map = some r :=
    keccak256_caches h
  have hlow : lowSlotBound ≤ r.val := hpost _ r hcached
  intro he
  rw [he] at hlow
  omega

/-! ## THE OFFSET FORM

`KeccakInjective.keccak256_add_ne_lowSlot` is the third axiom in this family: a keccak slot OFFSET by an array index
still never equals a low slot.  Deriving it needs one more thing from the pool than `NoLowInRange` gives — that
adding an array-sized offset does not WRAP.  Without that a slot near `2^256` could wrap down into the low range, and
the statement would be false.

So the configuration is a two-sided window: pool slots sit at least an array length above `0` and at least an array
length below `2^256`. -/

/-- Pool slots sit an array length clear of both ends of the word. -/
def RangeInWindow (σ : EVMState) : Prop :=
  ∀ x ∈ σ.keccak_range, lowSlotBound ≤ x.val ∧ x.val + lowSlotBound ≤ UInt256.size

/-- Cached slots sit an array length clear of both ends. -/
def CachedInWindow (σ : EVMState) : Prop :=
  ∀ (I : List UInt256) (v : UInt256), Finmap.lookup I σ.keccak_map = some v →
    lowSlotBound ≤ v.val ∧ v.val + lowSlotBound ≤ UInt256.size

/-- The pool only shrinks, so the window survives a step. -/
theorem rangeInWindow_keccakOut {σ : EVMState} {p n : UInt256}
    (hR : RangeInWindow σ) : RangeInWindow (keccakOut σ p n).2 := by
  intro x hx
  refine hR x ?_
  -- the post-state's range is a sublist of the pre-state's
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some w => rw [keccakOut_of_cached hl] at hx; exact hx
  | none =>
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun y => decide (y ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil =>
      have hpost : (keccakOut σ p n).2 = σ.addHashCollision := by
        unfold keccakOut EVMState.keccak256; simp only [hl, hpart]
      rw [hpost] at hx; exact hx
    | cons hd tl =>
      have hpost : (keccakOut σ p n).2
          = {σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p n) hd,
                    keccak_range := tl,
                    used_range := {hd} ∪ σ.used_range} := by
        unfold keccakOut EVMState.keccak256; simp only [hl, hpart]
      rw [hpost] at hx
      rw [List.partition_eq_filter_filter] at hpart
      have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
        ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
      exact List.mem_of_mem_filter (h2 ▸ List.mem_cons_of_mem hd hx)

/-- **PRESERVATION.**  Values entering the cache come from the pool, so the window is maintained. -/
theorem cachedInWindow_keccakOut {σ : EVMState} {p n : UInt256}
    (hR : RangeInWindow σ) (hC : CachedInWindow σ) : CachedInWindow (keccakOut σ p n).2 := by
  intro I v hv
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some w => rw [keccakOut_of_cached hl] at hv; exact hC I v hv
  | none =>
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun y => decide (y ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil =>
      have hpost : (keccakOut σ p n).2 = σ.addHashCollision := by
        unfold keccakOut EVMState.keccak256; simp only [hl, hpart]
      rw [hpost] at hv; exact hC I v hv
    | cons hd tl =>
      have hhd : hd ∈ σ.keccak_range := by
        rw [List.partition_eq_filter_filter] at hpart
        have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
          ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
        exact List.mem_of_mem_filter (h2 ▸ List.mem_cons_self hd tl)
      have hpost : (keccakOut σ p n).2
          = {σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p n) hd,
                    keccak_range := tl,
                    used_range := {hd} ∪ σ.used_range} := by
        unfold keccakOut EVMState.keccak256; simp only [hl, hpart]
      rw [hpost] at hv
      by_cases hI : I = mkInterval σ.machine_state p n
      · subst hI
        rw [Finmap.lookup_insert] at hv
        rw [← Option.some.inj hv]
        exact hR hd hhd
      · rw [Finmap.lookup_insert_of_ne _ hI] at hv
        exact hC I v hv

/-- **DROP-IN FOR `KeccakInjective.keccak256_add_ne_lowSlot`.**  A keccak slot offset by an array index never equals a
low slot.

The window is what makes the offset safe: `lowSlotBound ≤ r.val` puts the slot above the low range, and
`r.val + lowSlotBound ≤ size` stops the offset from wrapping back into it. -/
theorem keccak256_add_ne_lowSlot_of_config {σ σ' : EVMState} {p n r : UInt256} (j c : UInt256)
    (hR : RangeInWindow σ) (hC : CachedInWindow σ)
    (h : σ.keccak256 p n = some (r, σ'))
    (hj : j.val < lowSlotBound) (hc : c.val < lowSlotBound) : r + j ≠ c := by
  have hko : keccakOut σ p n = (r, σ') := by unfold keccakOut; rw [h]
  have hpost : CachedInWindow σ' := by
    have hn := cachedInWindow_keccakOut (σ := σ) (p := p) (n := n) hR hC
    rw [hko] at hn
    exact hn
  obtain ⟨hlo, hhi⟩ := hpost _ r (keccak256_caches h)
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hadd : (r + j).val = r.val + j.val := by
    have h1 : (r + j).val = (r.val + j.val) % UInt256.size := rfl
    rw [h1, Nat.mod_eq_of_lt (by unfold lowSlotBound at *; omega)]
  intro he
  have := congrArg Fin.val he
  rw [hadd] at this
  unfold lowSlotBound at *
  omega

/-- `mstore` preserves the pool window — it touches neither the range nor the cache. -/
theorem rangeInWindow_mstore {σ : EVMState} (a v : UInt256) (h : RangeInWindow σ) :
    RangeInWindow (σ.mstore a v) := h

/-- `mstore` preserves the cache window. -/
theorem cachedInWindow_mstore {σ : EVMState} (a v : UInt256) (h : CachedInWindow σ) :
    CachedInWindow (σ.mstore a v) := h

/-- `mstore` preserves the low-slot-free pool and cache. -/
theorem noLow_mstore {σ : EVMState} (a v : UInt256) (hR : NoLowInRange σ) (hC : NoLowCached σ) :
    NoLowInRange (σ.mstore a v) ∧ NoLowCached (σ.mstore a v) := ⟨hR, hC⟩

/-- The two-sided window implies the one-sided low-slot-freedom, for the pool. -/
theorem noLowInRange_of_window {σ : EVMState} (h : RangeInWindow σ) : NoLowInRange σ :=
  fun x hx => (h x hx).1

/-- The two-sided window implies the one-sided low-slot-freedom, for the cache. -/
theorem noLowCached_of_window {σ : EVMState} (h : CachedInWindow σ) : NoLowCached σ :=
  fun I v hv => (h I v hv).1

end Clear.KeccakLowSlot
