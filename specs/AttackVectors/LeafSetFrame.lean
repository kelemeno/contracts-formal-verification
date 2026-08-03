import specs.AttackVectors.ConcreteBridge

/-
  THE LEAF-SET FRAME.

  `AttackVectors.ConcreteBridge` reduces no-theft for the deployed insert path to
  `ConcreteLeafHistory`: every step is a leaf-set no-op or one guarded insert.
  Its header lists, as an out-of-scope obligation, that the NO-OP disjunct is a
  hypothesis — nothing yet shows the contract's OTHER entry points leave the leaf
  set alone.

  This file supplies the tool for discharging it.  `leafSetOf` reads exactly
  three kinds of storage location:

      slot 1                    the leaf count
      leafSlot σ n              the leaf struct's `value`   field  (keccak(n‖4))
      leafSlot σ n + 2          the leaf struct's `nextValue` field

  so a storage write that misses all of them cannot change the represented set.
  `leafSetOf_sstore_frame` is that statement; `leafSetOf_sstore_frame_noop` packages
  it as the no-op disjunct of `ConcreteLeafHistory`.

  Discharging the obligation for a given function is then a matter of showing its
  writes land outside those locations — which is what the separation lemmas in
  `imt_leaf_storage_user.lean` (base-4 vs base-5 preimages, low-slot separation)
  are for.

  NOTE ON THE CACHE HYPOTHESIS.  `leafSlot` is a keccak image, so it is only
  `sstore`-stable once the relevant preimage is cached (`leafSlot_sstore`).  The
  frame therefore requires cache witnesses for the indices in range — the same
  hypothesis shape `leafSetOf_imtInsert` and `leafSetOf_evolution_step` already
  carry, so callers that satisfy those satisfy this.

  Axiom-clean: propext / Quot.sound / Classical.choice only, verified with
  #print axioms.  Note this does NOT inherit the keccak idealizations —
  leafSlot_sstore is itself clean, since it argues from sstore leaving memory and
  the keccak cache untouched rather than from injectivity.
-/

namespace AttackVectors.LeafSetFrame

open Clear Clear.KeccakDeterminism IMTAbstract
open generated.L2InteropCommitmentTree.L2InteropCommitmentTree

/-- **THE LEAF-SET FRAME.**  A single storage write that touches neither the leaf
count (slot 1) nor any in-range leaf's `value` / `nextValue` slot leaves the
represented leaf set unchanged. -/
theorem leafSetOf_sstore_frame {σ : EVMState} {a v : UInt256}
    (hcount : a ≠ 1)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ w, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some w)
    (hval : ∀ m : ℕ, m < (σ.sload 1).val → a ≠ leafSlot σ (m : UInt256))
    (hnext : ∀ m : ℕ, m < (σ.sload 1).val → a ≠ leafSlot σ (m : UInt256) + 2) :
    leafSetOf (σ.sstore a v) = leafSetOf σ := by
  unfold leafSetOf
  -- the count is untouched, so the index range is the same
  have hc : ((σ.sstore a v).sload 1) = σ.sload 1 := sload_sstore_ne hcount
  rw [hc]
  -- and every in-range leaf decodes identically
  refine Finset.image_congr ?_
  intro m hm
  rw [Finset.mem_coe, Finset.mem_range] at hm
  obtain ⟨w, hw⟩ := hcaches m hm
  show decodeLeaf (σ.sstore a v) (m : UInt256) = decodeLeaf σ (m : UInt256)
  unfold decodeLeaf
  rw [leafSlot_sstore hw, sload_sstore_ne (hval m hm), sload_sstore_ne (hnext m hm)]

/-- **THE FRAME AS A `ConcreteLeafHistory` STEP.**  A step whose only storage
effect is such a write is exactly the no-op disjunct, so it can be handed
straight to `ConcreteBridge.imt_no_theft`. -/
theorem leafSetOf_sstore_frame_noop {σ σ' : EVMState} {a v : UInt256}
    (hstep : σ' = σ.sstore a v)
    (hcount : a ≠ 1)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ w, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some w)
    (hval : ∀ m : ℕ, m < (σ.sload 1).val → a ≠ leafSlot σ (m : UInt256))
    (hnext : ∀ m : ℕ, m < (σ.sload 1).val → a ≠ leafSlot σ (m : UInt256) + 2) :
    leafSetOf σ' = leafSetOf σ := by
  rw [hstep]
  exact leafSetOf_sstore_frame hcount hcaches hval hnext

/-! ## A worked instance: the `valueToIndex` write

The insert path also writes the `valueToIndex` mapping (base 5).  Everything
needed to frame that write past the leaf set already exists in
`imt_fidelity_user.lean` — `leafCount_vtiWrite` and `decodeLeaf_vtiWrite`, both
resting on base-4 vs base-5 preimage separation.  Composing them gives the
no-op disjunct for this write outright, with no side conditions beyond the cache
witnesses.

This is the pattern for every other entry point: prove the write misses slot 1
and the leaf fields, then conclude the leaf set is untouched. -/

/-- **THE `valueToIndex` WRITE DOES NOT MOVE THE LEAF SET.**  A concrete
instance of the frame: writing the `valueToIndex` entry for `v` leaves the
represented leaf set exactly as it was, so such a step satisfies the no-op
disjunct of `ConcreteLeafHistory`.

Unlike `leafSetOf_sstore_frame`, this DOES enlarge the trusted base — but only by
TWO of the four keccak idealizations, verified with #print axioms:
`keccak256_ne_lowSlot` (a keccak image is never a low reserved slot, used by
`leafCount_vtiWrite` to separate the write from slot 1) and `keccak256_slot_sep`
(used via `decodeLeaf_vtiWrite` for base-4 vs base-5 preimage separation).
Notably NOT `keccak256_inj`: distinguishing these two slot families does not
require full injectivity. -/
theorem leafSetOf_vtiWrite {σ : EVMState} {v u wv : UInt256}
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ w, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some w) :
    leafSetOf (σ.sstore (vtiSlot σ v) u) = leafSetOf σ := by
  unfold leafSetOf
  rw [leafCount_vtiWrite hcv]
  refine Finset.image_congr ?_
  intro m hm
  rw [Finset.mem_coe, Finset.mem_range] at hm
  obtain ⟨w, hw⟩ := hcaches m hm
  show decodeLeaf (σ.sstore (vtiSlot σ v) u) (m : UInt256) = decodeLeaf σ (m : UInt256)
  exact decodeLeaf_vtiWrite hcv hw

/-! ## Second instance: the Merkle node/zeros array writes

The insert path also writes the `_nodes` and `_zeros` arrays (bases 2 and 3),
addressed as `arrOut σ a + j`.  `decodeLeaf_arrWrite` already frames the leaf
fields past such a write; the missing half is the leaf COUNT, which follows from
a keccak image never landing on a reserved low slot. -/

/-- **The leaf count survives a node-array write.**  `arrOut σ a + j` is a keccak
image offset by a small `j`, so it is never the reserved slot 1. -/
theorem leafCount_arrWrite {σ : EVMState} {a j v wa : UInt256}
    (hca : Finmap.lookup (EVMState.mkInterval (σ.mstore 0 a).machine_state 0 32)
        σ.keccak_map = some wa)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound) :
    (σ.sstore ((arrOut σ a).1 + j) v).sload 1 = σ.sload 1 := by
  obtain ⟨hka, hva⟩ := arrOut_keccak hca
  refine sload_sstore_ne ?_
  rw [hva]
  exact Clear.KeccakInjective.keccak256_add_ne_lowSlot j 1 hka hj (by decide)

/-- **THE MERKLE ARRAY WRITES DO NOT MOVE THE LEAF SET.**  Writing a `_nodes` or
`_zeros` element leaves the represented leaf set exactly as it was, so every step
of the root-recomputation walk satisfies the no-op disjunct of
`ConcreteLeafHistory`.

This matters because the walk performs MANY such writes: it is the bulk of the
insert path's storage traffic, and none of it can disturb the leaf set that
no-theft is stated over. -/
theorem leafSetOf_arrWrite {σ : EVMState} {a j v wa : UInt256}
    (hca : Finmap.lookup (EVMState.mkInterval (σ.mstore 0 a).machine_state 0 32)
        σ.keccak_map = some wa)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ w, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some w) :
    leafSetOf (σ.sstore ((arrOut σ a).1 + j) v) = leafSetOf σ := by
  unfold leafSetOf
  rw [leafCount_arrWrite hca hj]
  refine Finset.image_congr ?_
  intro m hm
  rw [Finset.mem_coe, Finset.mem_range] at hm
  obtain ⟨w, hw⟩ := hcaches m hm
  show decodeLeaf (σ.sstore ((arrOut σ a).1 + j) v) (m : UInt256)
      = decodeLeaf σ (m : UInt256)
  exact decodeLeaf_arrWrite (σₐ := σ) hca hw hj

end AttackVectors.LeafSetFrame
