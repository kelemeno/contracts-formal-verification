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

end Clear.KeccakLowSlot
