import specs.KeccakFresh
import specs.KeccakInjective

/-
  SLOT SEPARATION — DERIVED FROM THE POOL, NOT AXIOMATIZED.

  The companion to `specs/KeccakLowSlot.lean`.  `Clear.KeccakInjective` posits `keccak256_slot_sep` as an AXIOM:
  slots for distinct preimages are separated by more than any array length, so an array element `keccak(P₁) + i`
  (small `i`) never coincides with another slot `keccak(P₂)`.

  As with the low-slot axiom, in Clear's model this is not a fact about keccak.  Every slot the model ever produces
  comes from `keccak_range`, so separation is a property of that POOL, and the invariant is inherited for a reason
  worth noting: the set of slots a state can produce only ever SHRINKS.  A step moves one element from the pool into
  the cache and discards the rest of the used prefix — it never introduces a slot from nowhere.  So `Separated` needs
  no preservation argument of its own beyond that monotonicity.

  Axiom-free; in particular independent of the `KeccakInjective` axioms, which this file imports only for
  `lowSlotBound`.
-/

namespace Clear.KeccakSlotSep

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakInjective EVMState

/-- The slots a state can produce: those already cached, and those still in the pool. -/
def Slots (σ : EVMState) (v : UInt256) : Prop :=
  (∃ I : List UInt256, Finmap.lookup I σ.keccak_map = some v) ∨ v ∈ σ.keccak_range

/-- Distinct producible slots are separated by more than any array length. -/
def Separated (σ : EVMState) : Prop :=
  ∀ x y : UInt256, Slots σ x → Slots σ y → x ≠ y →
    ∀ i : UInt256, i.val < lowSlotBound → x + i ≠ y

/-- **THE SLOT SET ONLY SHRINKS.**  A hash step introduces no slot that was not already producible: a hit changes
nothing, and a miss moves one pool element into the cache while discarding the rest of the used prefix. -/
theorem slots_keccakOut_subset {σ : EVMState} {p n v : UInt256}
    (h : Slots (keccakOut σ p n).2 v) : Slots σ v := by
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some w =>
    -- a hit leaves the state alone
    rw [keccakOut_of_cached hl] at h
    exact h
  | none =>
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil =>
      have hpost : (keccakOut σ p n).2 = σ.addHashCollision := by
        unfold keccakOut EVMState.keccak256
        simp only [hl, hpart]
      rw [hpost] at h
      exact h
    | cons hd tl =>
      have hhd : hd ∈ σ.keccak_range := by
        rw [List.partition_eq_filter_filter] at hpart
        have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
          ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
        exact List.mem_of_mem_filter (h2 ▸ List.mem_cons_self hd tl)
      have htl : ∀ y ∈ tl, y ∈ σ.keccak_range := by
        intro y hy
        rw [List.partition_eq_filter_filter] at hpart
        have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
          ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
        exact List.mem_of_mem_filter (h2 ▸ List.mem_cons_of_mem hd hy)
      have hpost : (keccakOut σ p n).2
          = {σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p n) hd,
                    keccak_range := tl,
                    used_range := {hd} ∪ σ.used_range} := by
        unfold keccakOut EVMState.keccak256
        simp only [hl, hpart]
      rw [hpost] at h
      rcases h with ⟨I, hI⟩ | hrange
      · by_cases hIe : I = mkInterval σ.machine_state p n
        · subst hIe
          rw [Finmap.lookup_insert] at hI
          rw [← Option.some.inj hI]
          exact Or.inr hhd
        · rw [Finmap.lookup_insert_of_ne _ hIe] at hI
          exact Or.inl ⟨I, hI⟩
      · exact Or.inr (htl v hrange)

/-- **PRESERVATION, BY MONOTONICITY.**  Separation of a shrinking set is inherited. -/
theorem separated_keccakOut {σ : EVMState} {p n : UInt256}
    (hsep : Separated σ) : Separated (keccakOut σ p n).2 :=
  fun x y hx hy hne i hi =>
    hsep x y (slots_keccakOut_subset hx) (slots_keccakOut_subset hy) hne i hi

/-- A step's value is a slot the state could produce.  Non-exhaustion is needed: an exhausted pool returns `0`,
which need not be producible at all. -/
theorem keccakOut_val_slot {σ : EVMState} {p n : UInt256}
    (hfuel : (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ []) :
    Slots σ (keccakOut σ p n).1 := by
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some w =>
    rw [keccakOut_of_cached hl]
    exact Or.inl ⟨_, hl⟩
  | none =>
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil => rw [hpart] at hfuel; exact absurd rfl hfuel
    | cons hd tl =>
      have hval : (keccakOut σ p n).1 = hd := by
        unfold keccakOut EVMState.keccak256
        simp only [hl, hpart]
      rw [hval]
      right
      rw [List.partition_eq_filter_filter] at hpart
      have h2 : hd :: tl = σ.keccak_range.filter (fun z => !decide (z ∈ σ.used_range)) :=
        ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
      exact List.mem_of_mem_filter (h2 ▸ List.mem_cons_self hd tl)

/-- **SLOT SEPARATION, PROVED.**  A step's value, offset by anything smaller than an array length, never coincides
with a different producible slot — so an array element hanging off one slot cannot reach another.

This is `keccak256_slot_sep`'s content, obtained from the pool's configuration instead of from an idealization about
hash values. -/
theorem keccakOut_add_ne_slot {σ : EVMState} {p n v : UInt256}
    (hsep : Separated σ)
    (hfuel : (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ [])
    (hv : Slots σ v) (hne : (keccakOut σ p n).1 ≠ v)
    (i : UInt256) (hi : i.val < lowSlotBound) :
    (keccakOut σ p n).1 + i ≠ v :=
  hsep _ v (keccakOut_val_slot hfuel) hv hne i hi

/-- **DROP-IN FOR `KeccakInjective.keccak256_slot_sep`.**  A successful keccak call's slot, offset by less than an
array length, never coincides with a different producible slot.

As with the low-slot companion, `h` witnesses that the call succeeded, so no non-exhaustion hypothesis is needed —
what remains is exactly the pool's separation. -/
theorem keccak256_slot_sep_of_config {σ σ' : EVMState} {p n r v : UInt256}
    (hsep : Separated σ) (h : σ.keccak256 p n = some (r, σ'))
    (hv : Slots σ v) (hne : r ≠ v)
    (i : UInt256) (hi : i.val < lowSlotBound) : r + i ≠ v := by
  have hko : keccakOut σ p n = (r, σ') := by unfold keccakOut; rw [h]
  -- the call's own result is cached in the post-state, hence producible in the pre-state
  have hcached : Finmap.lookup (mkInterval σ.machine_state p n) σ'.keccak_map = some r :=
    keccak256_caches h
  have hrslot : Slots σ r := by
    refine slots_keccakOut_subset (σ := σ) (p := p) (n := n) ?_
    rw [hko]
    exact Or.inl ⟨_, hcached⟩
  exact hsep r v hrslot hv hne i hi

/-! ## THE TWO-SIDED OFFSET FORM

`imt_root_atlas_user`'s `keccak_off_ne_off` compares two slots BOTH offset by small amounts: `r₁ + k₁ ≠ r₂ + k₂`.
It needs no two-sided separation notion — the offset difference can be absorbed into one side, reducing it to the
one-sided `Separated`.  That is the trick the original proof uses, and it works verbatim here.

At the real call sites both slots arrive as CACHE HITS (the callers hold `Finmap.lookup … = some r`), so this form
takes hits rather than `keccak256 … = some`.  That is what makes `r₁ ≠ r₂` immediate — `CacheInj` turns the
preimages' inequality into the slots' — and it also makes both slots visibly producible. -/

/-- **DROP-IN FOR `keccak_off_ne_off`.**  Two cached slots with distinct preimages stay distinct under any two
array-sized offsets.

Both cryptographic ingredients are the derived ones: `CacheInj` for slot distinctness, `Separated` for the offsets. -/
theorem cached_off_ne_off {σ : EVMState} {I₁ I₂ : List UInt256} {r₁ r₂ k₁ k₂ : UInt256}
    (hsep : Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hc₁ : Finmap.lookup I₁ σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup I₂ σ.keccak_map = some r₂)
    (hne : I₁ ≠ I₂)
    (hs₁ : k₁.val < lowSlotBound) (hs₂ : k₂.val < lowSlotBound) :
    r₁ + k₁ ≠ r₂ + k₂ := by
  have hslot₁ : Slots σ r₁ := Or.inl ⟨I₁, hc₁⟩
  have hslot₂ : Slots σ r₂ := Or.inl ⟨I₂, hc₂⟩
  have hrne : r₁ ≠ r₂ := by
    intro he
    exact hne (hinj I₁ I₂ r₁ hc₁ (he ▸ hc₂))
  intro heq
  rcases Nat.le_total k₁.val k₂.val with hle | hle
  · -- absorb `k₂ - k₁` into `r₂`
    set d : UInt256 := ((k₂.val - k₁.val : ℕ) : UInt256) with hdef
    have hd : d.val = k₂.val - k₁.val :=
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) k₂.isLt)
    have hdlt : d.val < lowSlotBound := by rw [hd]; omega
    have hk2eq : k₁ + d = k₂ := by
      apply Fin.ext
      show (k₁.val + d.val) % UInt256.size = k₂.val
      rw [hd, Nat.add_sub_cancel' hle]
      exact Nat.mod_eq_of_lt k₂.isLt
    have hcancel : r₁ = r₂ + d := by
      refine add_right_cancel (b := k₁) ?_
      calc r₁ + k₁ = r₂ + k₂ := heq
        _ = r₂ + (k₁ + d) := by rw [hk2eq]
        _ = r₂ + d + k₁ := by ring
    exact hsep r₂ r₁ hslot₂ hslot₁ (Ne.symm hrne) d hdlt hcancel.symm
  · -- symmetric: absorb `k₁ - k₂` into `r₁`
    set d : UInt256 := ((k₁.val - k₂.val : ℕ) : UInt256) with hdef
    have hd : d.val = k₁.val - k₂.val :=
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) k₁.isLt)
    have hdlt : d.val < lowSlotBound := by rw [hd]; omega
    have hk1eq : k₂ + d = k₁ := by
      apply Fin.ext
      show (k₂.val + d.val) % UInt256.size = k₁.val
      rw [hd, Nat.add_sub_cancel' hle]
      exact Nat.mod_eq_of_lt k₁.isLt
    have hcancel : r₁ + d = r₂ := by
      refine add_right_cancel (b := k₂) ?_
      calc r₁ + d + k₂ = r₁ + (k₂ + d) := by ring
        _ = r₁ + k₁ := by rw [hk1eq]
        _ = r₂ + k₂ := heq
    exact hsep r₁ r₂ hslot₁ hslot₂ hrne d hdlt hcancel

/-! ## DIFFERENT PREIMAGE SHAPES

A Solidity ARRAY element sits at `keccak(base) + i` — a 32-byte preimage, offset by the index.  A
MAPPING entry sits at `keccak(key ‖ base)` — a 64-byte preimage.  Whether those two families can
collide is the remaining storage-shape question, and it is what makes reasoning about an array write
without mentioning mappings sound.

They cannot, and the reason needs no cryptography: preimages of different LENGTHS are different lists,
which `KeccakInjective.mkInterval_ne_of_len_ne` establishes by `List.length` alone (that lemma is
axiom-free despite its home — it depends only on `propext` and `Quot.sound`).  Feed that inequality to
`cached_off_ne_off` and the offsets are handled too. -/

/-- **PREIMAGES OF DIFFERENT LENGTHS GIVE SEPARATED SLOTS.**  Two cached hashes whose preimage windows
have different byte-lengths stay distinct under any two array-sized offsets.

The 32-vs-64 instance is array-element vs mapping-entry: no array write can reach a mapping entry, and
no mapping write can reach an array element. -/
theorem cached_off_ne_off_of_len_ne {σ : EVMState} {ms₁ ms₂ : MachineState}
    (hsep : Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    {p₁ n₁ p₂ n₂ r₁ r₂ k₁ k₂ : UInt256}
    (hc₁ : Finmap.lookup (mkInterval ms₁ p₁ n₁) σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup (mkInterval ms₂ p₂ n₂) σ.keccak_map = some r₂)
    (hlen : n₁.val ≠ n₂.val)
    (hk₁ : k₁.val < lowSlotBound) (hk₂ : k₂.val < lowSlotBound) :
    r₁ + k₁ ≠ r₂ + k₂ :=
  cached_off_ne_off hsep hinj hc₁ hc₂
    (Clear.KeccakInjective.mkInterval_ne_of_len_ne hlen) hk₁ hk₂

/-- **AN ARRAY WRITE CANNOT REACH A MAPPING ENTRY.**  The frame form at the 32-vs-64 instance: storing
into an array element leaves every mapping entry exactly as it was. -/
theorem arr_write_frames_mapping {σ σ_w : EVMState} {ms₁ ms₂ : MachineState}
    (hsep : Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    {p₁ p₂ r₁ r₂ i v : UInt256}
    (hc₁ : Finmap.lookup (mkInterval ms₁ p₁ 32) σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup (mkInterval ms₂ p₂ 64) σ.keccak_map = some r₂)
    (hi : i.val < lowSlotBound) :
    (σ_w.sstore (r₁ + i) v).sload r₂ = σ_w.sload r₂ := by
  refine Clear.KeccakDistinct.sload_sstore_of_ne σ_w ?_
  intro he
  refine cached_off_ne_off_of_len_ne hsep hinj hc₁ hc₂ (by decide) hi
    (show ((0 : UInt256)).val < lowSlotBound by decide) ?_
  rw [add_zero]
  exact he.symm

end Clear.KeccakSlotSep
