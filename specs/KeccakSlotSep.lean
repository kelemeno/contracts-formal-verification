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

end Clear.KeccakSlotSep
