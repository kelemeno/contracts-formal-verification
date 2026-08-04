import specs.LeafHashBridge
import specs.FoldCacheInv
import specs.AtomicFlowManager.AtomicFlowManager.exclusivity_user

/-
  A COMMITTED LEAF'S ROOT IS A TREE ROOT — the last link, and what still blocks it.

  `AttackVectors.CrossContract` discharges the AFM exclusivity capstone's `GapSound` obligation but
  leaves `habs`: that every leaf committed under a published root `R` really is a member of the
  represented leaf set.  `AttackVectors.RootBindingFull` now proves root binding for the deployed
  hashes.  Wiring the two together means turning a `CommittedLeafAt` witness into the `getD`-shaped
  premise root binding consumes.

  ## A FINDING ABOUT `CommittedLeafAt`

  It cannot be done for `CommittedLeafAt` as defined.  That predicate existentially quantifies the
  fold's STARTING LEVEL `iv`:

      ∃ … (iv : UInt256), (foldRoot σf p d iv idx (hashLeafOut σh leaf).1).1 = R

  so a witness need not correspond to a level-0 walk at all — it may be a fold begun partway up a
  path.  The fold correspondence (`FoldCacheInv`) speaks about `iv = 0`, and nothing recovers a
  level-0 walk from a fold starting elsewhere: the intermediate accumulator is unconstrained.

  This makes `committed_member_gap_impossible` SOUND but its `habs` unnecessarily hard — the
  hypothesis quantifies over more witnesses than the contract can produce.  `CommittedLeafAt0`
  below pins `iv = 0`; it implies `CommittedLeafAt`, so any capstone proved from the weaker
  hypothesis still applies.

  ## WHAT THIS FILE PROVES, AND WHAT IT DOES NOT

  It proves that a level-0 committed leaf's root IS a tree root with that leaf's hash at its index
  (`committed_root_is_treeRoot`), and that the committed leaf's hash is the one the R7 results
  describe (`committed_leafhash_modelled`).

  It does NOT finish `habs`.  Two steps remain, both named at the bottom of this file.  Axiom-free.
-/

namespace AttackVectors.CommittedRoot

open Clear Clear.CachedHash Clear.LeafHashBridge Clear.LeafHashWindow Clear.FoldCacheInv
open MerkleSpec
open generated.AtomicFlowManager.AtomicFlowManager

set_option maxHeartbeats 1600000

/-- `CommittedLeafAt` with the fold pinned to start at level `0` — the only form the contract's own
path fold produces, and the only form the fold correspondence can speak about. -/
def CommittedLeafAt0 (R : UInt256) (d : ℕ) (idx key nk : UInt256) : Prop :=
  ∃ (σh : EVMState) (leaf : UInt256) (σf : EVMState) (p : UInt256),
    (hashLeafOut σh leaf).2.hash_collision = false ∧
    (σh.mload 64).val + 128 ≤ 18446744073709551615 ∧
    96 ≤ (σh.mload 64).val ∧
    (foldRoot σf p d 0 idx (hashLeafOut σh leaf).1).2.hash_collision = false ∧
    (foldRoot σf p d 0 idx (hashLeafOut σh leaf).1).1 = R ∧
    σh.mload leaf = key ∧ σh.mload (leaf + 64) = nk

/-- **THE PINNED FORM IS STRONGER.**  So a capstone conditional on `habs` for `CommittedLeafAt`
still applies once `habs` is proved only for level-0 witnesses — the weaker hypothesis covers
them. -/
theorem committedLeafAt_of_zero {R : UInt256} {d : ℕ} {idx key nk : UInt256}
    (h : CommittedLeafAt0 R d idx key nk) : CommittedLeafAt R d idx key nk := by
  obtain ⟨σh, leaf, σf, p, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨σh, leaf, σf, p, 0, h1, h2, h3, h4, h5, h6, h7⟩

/-- **THE COMMITTED LEAF'S HASH IS THE MODELLED ONE.**  `CommittedLeafAt`'s own two memory
hypotheses are exactly what the bridge needs, so no extra assumption is incurred: the committed
leaf's hash is `LeafHashWindow.leafHashOut` at the free pointer, and every R7 result applies to
it. -/
theorem committed_leafhash_modelled {σh : EVMState} {leaf : UInt256}
    (hpb : (σh.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σh.mload 64).val) :
    (hashLeafOut σh leaf).1
      = (leafHashOut σh (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
          (σh.mload (leaf + 64))).1 :=
  hashLeafOut_eq_leafHashOut hplow (by omega)
    (leafScratch_length_readback hpb hplow)

/-- **A COMMITTED LEAF'S ROOT IS A TREE ROOT.**  For a level-0 witness whose fold satisfies the
concrete fold invariant, the published root `R` is exactly the root of the tree over `L` with the
committed leaf's hash written at `idx`.

The witness components are taken explicitly rather than packed, because the fold-side hypotheses
have to be stated about the witness's own states — which an existential hides. -/
theorem committed_root_is_treeRoot
    {SF σh σf : EVMState} {leaf p idx R z0 : UInt256} {d : ℕ}
    {sibs : ℕ → UInt256} {L : List UInt256}
    (hfold : (foldRoot σf p d 0 idx (hashLeafOut σh leaf).1).1 = R)
    (hd : d < 2 ^ 256) (hpath : 96 ≤ p.val)
    (hpbnd : p.val + 32 * d + 64 ≤ UInt256.size)
    (hg : CacheInv SF p sibs idx (hashLeafOut σh leaf).1 d σf 0 idx
      (hashLeafOut σh leaf).1 d)
    (hidx : idx.val < L.length) (hcap : L.length ≤ 2 ^ d)
    (hsibs : ∀ l, l < d →
      sibs l = (levels (hashOf SF) z0 (L.set idx.val (hashLeafOut σh leaf).1) l).getD
        (sibIdx (idx.val / 2 ^ l)) (zeros (hashOf SF) z0 l)) :
    R = rootOf (hashOf SF) z0 (L.set idx.val (hashLeafOut σh leaf).1) d := by
  rw [← hfold]
  exact foldRoot_eq_rootOf_cached z0 hd hpath hpbnd hg hidx hcap hsibs

/-- **TWO COMMITTED LEAVES UNDER ONE ROOT AGREE ON THE WHOLE TREE.**  If two level-0 witnesses
publish the same `R` over the same leaf list and height, the two updated leaf lists have equal
roots — the `hroot` premise root binding consumes, obtained without assuming anything more.

This is the shape that makes `RootBindingFull.root_binding_fully_cached` applicable: one of the two
lists plays `claimed`, the other `leaves`. -/
theorem committed_roots_agree
    {SF σh σh' σf σf' : EVMState} {leaf leaf' p p' idx idx' R z0 : UInt256} {d : ℕ}
    {sibs sibs' : ℕ → UInt256} {L : List UInt256}
    (hfold : (foldRoot σf p d 0 idx (hashLeafOut σh leaf).1).1 = R)
    (hfold' : (foldRoot σf' p' d 0 idx' (hashLeafOut σh' leaf').1).1 = R)
    (hd : d < 2 ^ 256)
    (hpath : 96 ≤ p.val) (hpbnd : p.val + 32 * d + 64 ≤ UInt256.size)
    (hpath' : 96 ≤ p'.val) (hpbnd' : p'.val + 32 * d + 64 ≤ UInt256.size)
    (hg : CacheInv SF p sibs idx (hashLeafOut σh leaf).1 d σf 0 idx (hashLeafOut σh leaf).1 d)
    (hg' : CacheInv SF p' sibs' idx' (hashLeafOut σh' leaf').1 d σf' 0 idx'
      (hashLeafOut σh' leaf').1 d)
    (hidx : idx.val < L.length) (hidx' : idx'.val < L.length) (hcap : L.length ≤ 2 ^ d)
    (hsibs : ∀ l, l < d →
      sibs l = (levels (hashOf SF) z0 (L.set idx.val (hashLeafOut σh leaf).1) l).getD
        (sibIdx (idx.val / 2 ^ l)) (zeros (hashOf SF) z0 l))
    (hsibs' : ∀ l, l < d →
      sibs' l = (levels (hashOf SF) z0 (L.set idx'.val (hashLeafOut σh' leaf').1) l).getD
        (sibIdx (idx'.val / 2 ^ l)) (zeros (hashOf SF) z0 l)) :
    rootOf (hashOf SF) z0 (L.set idx.val (hashLeafOut σh leaf).1) d
      = rootOf (hashOf SF) z0 (L.set idx'.val (hashLeafOut σh' leaf').1) d := by
  rw [← committed_root_is_treeRoot hfold hd hpath hpbnd hg hidx hcap hsibs,
      ← committed_root_is_treeRoot hfold' hd hpath' hpbnd' hg' hidx' hcap hsibs']

/-! ## WHAT REMAINS FOR `habs`

Two steps, neither a rephrasing:

1. ~~**The committed leaf's hash must be recognised as `lh3`.**~~  CLOSED below by
   `committed_leafhash_is_cached`: the keccak step and the cache read coincide on a cache hit
   (`LeafHashWindow.leafHashOut_eq_leafHashOf_of_cached`), so this costs only a cache-presence fact
   about the witness — no new assumption about keccak.

2. **The tree's own leaf list must be tied to `leafSetOf`.**  Root binding concludes membership in
   `leafSetOf σ` from `hleaves`, the pointwise claim that `leaves` is the tree's leaf-hash list.
   Nothing here produces `hleaves`: it relates STORAGE (`decodeLeaf3`) to the list the fold's
   siblings came from, which is a storage/memory correspondence for the sibling array — the
   `arrWindow` track (blueprint R0), not this one.

Step 2 is the substantive one, and it is the same obligation the abstract chain has always carried
under the name `habs`.  What has changed is that everything AROUND it is now concrete.
-/

/-! ## STEP 1, CLOSED

`LeafHashWindow.leafHashOut_eq_leafHashOf_of_cached` shows the keccak step and the cache-derived hash
coincide on a cache hit.  Composing it with the deployed bridge recognises a COMMITTED leaf's hash as
the cache-derived one — which is exactly `LeafDecode3.lh3` at the leaf's three fields, definitionally.

So root binding's `hclaim` premise is now obtainable from a witness plus one cache-presence fact, and
step 1 of the two named below is closed. -/

/-- **THE COMMITTED LEAF'S HASH IS THE CACHE-DERIVED HASH.**  For a committed leaf whose preimage the
hashing state already holds — the situation after that state hashed it — the value the contract
computed is `leafHashOf` at the leaf's three fields.

`LeafDecode3.lh3 σh P ⟨v, ni, nv⟩` unfolds to exactly the right-hand side, so this is the `hclaim`
premise of `RootBindingFull.root_binding_fully_cached`, with no assumption beyond cache presence. -/
theorem committed_leafhash_is_cached {σh : EVMState} {leaf : UInt256} {r : UInt256}
    (hpb : (σh.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σh.mload 64).val)
    (hc : Finmap.lookup
      (leafInterval σh (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
        (σh.mload (leaf + 64))) σh.keccak_map = some r) :
    (hashLeafOut σh leaf).1
      = leafHashOf σh (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
          (σh.mload (leaf + 64)) := by
  rw [committed_leafhash_modelled hpb hplow]
  exact leafHashOut_eq_leafHashOf_of_cached hc

/-- The same, delivering the cached VALUE directly — the form that instantiates a `getD` premise. -/
theorem committed_leafhash_eq_cached_value {σh : EVMState} {leaf : UInt256} {r : UInt256}
    (hpb : (σh.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σh.mload 64).val)
    (hc : Finmap.lookup
      (leafInterval σh (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
        (σh.mload (leaf + 64))) σh.keccak_map = some r) :
    (hashLeafOut σh leaf).1 = r := by
  rw [committed_leafhash_is_cached hpb hplow hc, leafHashOf_eq_of_cached hc]

end AttackVectors.CommittedRoot
