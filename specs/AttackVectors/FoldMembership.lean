import specs.TreeFoldPins
import specs.AttackVectors.LeafHashList

/-
  FROM AN ACCEPTED FOLD TO ABSTRACT MEMBERSHIP — the `habs` route, with free siblings.

  `TreeFoldPins.fold_accept_pins_leaf` says an accepted proof's claimed leaf HASH is the tree's own hash at the
  opened index.  `LeafDecode3.lh3_inj_on_cached` turns equal hashes into equal LEAVES.  Composing them gives
  what the security layer consumes:

      a leaf whose claim the contract's fold accepts against the tree's published root
      is a member of the represented leaf set

  and unlike the `RootBindingFull` route this does NOT go through root-list injectivity — it goes down the
  PATH, so the attacker is free to choose every sibling and nothing assumes its pairs were ever hashed.

  One hypothesis serves both halves: `CacheInj SF`, keccak injective on the preimages the reference state has
  hashed.

  The leaf list is taken ABSTRACTLY, characterised pointwise by `hL`, rather than as
  `LeafHashList.leafHashList` applied to the tree.  That is not stylistic: instantiating it directly makes the
  elaborator unify a term containing `σtree.sload 1` inside a long application and it does not terminate at
  2,000,000 heartbeats.  `LeafHashList.leafHashList` satisfies `hL` by `leafHashList_getD_any`, so nothing is
  lost.  Axiom-free.
-/

namespace AttackVectors.FoldMembership

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakFuel Clear.CachedHash
open Clear.TreeFoldPins
open AttackVectors.LeafDecode3 AttackVectors.LeafHashList
open MerkleSpec

set_option maxHeartbeats 2000000

/-- `leafHashList`'s entries do not depend on the `getD` default, in range — so it satisfies the `hL`
characterization below at any default, including `MerkleSpec`'s `zeros`. -/
theorem leafHashList_getD_any {SF σ : EVMState} {p : UInt256} {n j : ℕ} (d : UInt256)
    (hj : j < n) :
    (leafHashList SF σ p n).getD j d = lh3 SF p (decodeLeaf3 σ (j : UInt256)) := by
  unfold leafHashList
  rw [List.getD_eq_get?, List.get?_map, List.get?_range hj]
  rfl

/-- **AN ACCEPTED FOLD PROVES MEMBERSHIP.**  If the contract's fold accepts `Lc`'s leaf hash against the
published root of a list that IS the tree's leaf-hash list, then `Lc`'s abstract projection is in the
represented leaf set.

The attacker supplies the whole path array; nothing assumes its pairs were ever hashed.  The only
cryptographic hypothesis is `CacheInj SF`, which serves both the descent and leaf-hash injectivity.

The opened index is a `ℕ` and the fold is applied at `(i : UInt256)`.  That is not cosmetic: taking a
`UInt256` index and passing `idx.val` to the membership lemma makes the elaborator unify
`((idx.val : ℕ) : UInt256)` with `idx`, i.e. reduce `idx.val % 2 ^ 256` at a 78-digit modulus, and it does not
terminate at 2,000,000 heartbeats.  Indexing by `ℕ` throughout avoids the round trip. -/
theorem fold_accept_implies_member
    {SF σtree : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (z0 path : UInt256) (height : ℕ) (i : ℕ) (cur : UInt256)
    {L : List UInt256}
    (hisz : i < UInt256.size)
    (hLlen : L.length = (σtree.sload 1).val)
    (hL : ∀ j : ℕ, j < (σtree.sload 1).val →
      L.getD j z0 = lh3 SF p (decodeLeaf3 σtree (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hidx : i < (σtree.sload 1).val)
    (hchain : ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1)))
    (haccept : (generated.AtomicFlowManager.AtomicFlowManager.foldRoot SF path height 0
        (i : UInt256) cur).1 = rootOf (hashOf SF) z0 L height)
    {Lc : Leaf3}
    (hCc : Cached SF p Lc) (hCi : Cached SF p (decodeLeaf3 σtree (i : UInt256)))
    (hcurLc : cur = lh3 SF p Lc) :
    Lc.toAbs ∈ generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf σtree := by
  have hival : ((i : UInt256)).val = i := Fin.val_cast_of_lt hisz
  have hidxL : ((i : UInt256)).val < L.length := by rw [hival, hLlen]; exact hidx
  have hpin : cur = L.getD ((i : UInt256)).val z0 :=
    fold_accept_pins_leaf z0 path L height 0 (i : UInt256) cur hinv hinj hfuel hne hcap hidxL
      hchain haccept
  rw [hival] at hpin
  have heq : lh3 SF p (decodeLeaf3 σtree (i : UInt256)) = lh3 SF p Lc :=
    (hpin.trans (hL i hidx)).symm.trans hcurLc
  exact mem_leafSetOf_of_hash_eq_restricted (lh3_inj_on_cached hnw hinj) hidx hCi hCc heq

/-- **REJECTION.**  A leaf whose projection is absent from the represented set cannot have its hash accepted
by the fold against the tree's published root — by any path. -/
theorem fold_rejects_non_member
    {SF σtree : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (z0 path : UInt256) (height : ℕ) (i : ℕ) (cur : UInt256)
    {L : List UInt256}
    (hisz : i < UInt256.size)
    (hLlen : L.length = (σtree.sload 1).val)
    (hL : ∀ j : ℕ, j < (σtree.sload 1).val →
      L.getD j z0 = lh3 SF p (decodeLeaf3 σtree (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hidx : i < (σtree.sload 1).val)
    (hchain : ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1)))
    {Lc : Leaf3}
    (hCc : Cached SF p Lc) (hCi : Cached SF p (decodeLeaf3 σtree (i : UInt256)))
    (hnot : Lc.toAbs ∉ generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf σtree)
    (hcurLc : cur = lh3 SF p Lc) :
    (generated.AtomicFlowManager.AtomicFlowManager.foldRoot SF path height 0 (i : UInt256) cur).1
      ≠ rootOf (hashOf SF) z0 L height :=
  fun haccept => hnot (fold_accept_implies_member hnw z0 path height i cur hisz hLlen hL hinv hinj
    hfuel hne hcap hidx hchain haccept hCc hCi hcurLc)

end AttackVectors.FoldMembership
