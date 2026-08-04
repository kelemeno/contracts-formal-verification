import specs.AttackVectors.RootBindingFull

/-
  STEP 2, RE-EXAMINED: `hleaves` IS A CONSTRUCTION, NOT AN OBLIGATION.

  `d6ce7c5` named the remaining `habs` step as "tying the tree's own leaf list to `leafSetOf`",
  meaning root binding's

      hleaves : ∀ j < (σ.sload 1).val, leaves.getD j 0 = lh3 SF p (decodeLeaf3 σ j)

  Looking at it again: this does not have to be PROVED of a given list — it characterises which list
  is meant, and that list can simply be BUILT.  `leafHashList` below is it, and `hleaves` then holds
  by computation.  So this hypothesis disappears from the chain rather than being discharged.

  That re-identifies what is actually left.  It is `hsibs`: that the fold's sibling stream holds the
  tree's level nodes,

      sibs l = (levels (hashOf SF) z0 leaves l).getD (sibIdx (idx / 2^l)) (zeros …)

  which relates the contract's path ARRAY IN MEMORY to the tree's levels.  That is a genuine
  storage/memory correspondence — the `arrWindow` track — and it is the only remaining premise of the
  root-binding chain that is neither a construction nor a cache-presence fact.

  Axiom-free.
-/

namespace AttackVectors.LeafHashList

open Clear Clear.CachedHash Clear.MerkleCachedInj Clear.RootBindingCached
open AttackVectors.LeafDecode3 AttackVectors.RootBindingFull
open generated.L2InteropCommitmentTree.L2InteropCommitmentTree

/-- **THE TREE'S LEAF-HASH LIST, BUILT FROM STORAGE.**  Entry `j` is the deployed leaf hash of the
leaf decoded from storage at index `j`. -/
def leafHashList (SF σ : EVMState) (p : UInt256) (n : ℕ) : List UInt256 :=
  (List.range n).map (fun j : ℕ => lh3 SF p (decodeLeaf3 σ (j : UInt256)))

@[simp] theorem leafHashList_length (SF σ : EVMState) (p : UInt256) (n : ℕ) :
    (leafHashList SF σ p n).length = n := by
  unfold leafHashList; rw [List.length_map, List.length_range]

/-- Entry `j` is what it says it is. -/
theorem leafHashList_getD {SF σ : EVMState} {p : UInt256} {n j : ℕ} (hj : j < n) :
    (leafHashList SF σ p n).getD j 0 = lh3 SF p (decodeLeaf3 σ (j : UInt256)) := by
  unfold leafHashList
  rw [List.getD_eq_get? , List.get?_map, List.get?_range hj]
  rfl

/-- **`hleaves` HOLDS BY CONSTRUCTION.**  So root binding's leaf-list characterization is not an
obligation on a run — it names a list, and the list exists. -/
theorem leafHashList_hleaves (SF σ : EVMState) (p : UInt256) :
    ∀ j : ℕ, j < (σ.sload 1).val →
      (leafHashList SF σ p (σ.sload 1).val).getD j 0 = lh3 SF p (decodeLeaf3 σ (j : UInt256)) :=
  fun _ hj => leafHashList_getD hj

/-- **ROOT BINDING FROM STORAGE.**  `RootBindingFull.root_binding_fully_cached` with the leaf list
supplied rather than hypothesized: a leaf that any list carrying the tree's published root places at
an in-range index really is a leaf of the represented set.

Compared with `root_binding_fully_cached`, the `hleaves` premise is gone.  What is left is: one
cryptographic hypothesis (`hcinj`), cache-presence facts about which preimages the reference state
hashed, the published-root agreement a verifier checks, and width/layout side conditions. -/
theorem root_binding_from_storage
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    (z0 : UInt256)
    {σ : EVMState} {height : ℕ} {claimed : List UInt256}
    (hlen : claimed.length = (σ.sload 1).val) (hne : claimed.length ≠ 0)
    (hcap : claimed.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height,
      PairsOK (CachedPair SF) (MerkleSpec.zeros (hashOf SF) z0 l)
        (MerkleSpec.levels (hashOf SF) z0 claimed l))
    (hp₂ : ∀ l < height,
      PairsOK (CachedPair SF) (MerkleSpec.zeros (hashOf SF) z0 l)
        (MerkleSpec.levels (hashOf SF) z0 (leafHashList SF σ p (σ.sload 1).val) l))
    (hroot : MerkleSpec.rootOf (hashOf SF) z0 claimed height
      = MerkleSpec.rootOf (hashOf SF) z0 (leafHashList SF σ p (σ.sload 1).val) height)
    {L : Leaf3} {i : ℕ} (hi : i < (σ.sload 1).val)
    (hCi : Cached SF p (decodeLeaf3 σ (i : UInt256))) (hCL : Cached SF p L)
    (hclaim : claimed.getD i 0 = lh3 SF p L) :
    L.toAbs ∈ leafSetOf σ :=
  root_binding_fully_cached hnw hcinj z0 (leafHashList_hleaves SF σ p)
    (by rw [hlen, leafHashList_length]) hne hcap hp₁ hp₂ hroot hi hCi hCL hclaim

end AttackVectors.LeafHashList
