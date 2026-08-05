import specs.AttackVectors.FoldMembership
import specs.AttackVectors.CommittedRoot

/-
  A COMMITTED WITNESS'S LEAF IS A MEMBER — `habs`, assembled.

  `CommittedLeafAt`'s witness data is exactly what the two preceding results consume:

    `CommittedRoot.committed_leafhash_in_fold_state`  the witness's leaf hash, recognised in the fold's state
    `FoldMembership.fold_accept_implies_member`       an accepted fold proves abstract membership

  and its abstract leaf `⟨key, nk⟩` is *definitionally* the `toAbs` of the three-field leaf read from memory:
  `key = mload leaf` is the `value` field and `nk = mload (leaf + 64)` the `nextValue` field, which is what
  `Leaf3.toAbs` keeps.

  So this file states the discharge for a witness given EXPLICITLY rather than packed.  That is deliberate:
  `CommittedLeafAt` hides its states behind existentials, so a version taking the packed predicate would have
  to assume its own side conditions uniformly over all witnesses — which is assuming what is to be proved.
  With the witness explicit, every hypothesis is a checkable fact about that run.

  Written under the gap-0 discipline (see AGENTS.md): the index is a `ℕ`, and neither generated namespace is
  opened.  Axiom-free.
-/

namespace AttackVectors.WitnessMember

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakFuel Clear.CachedHash
open Clear.LeafHashWindow Clear.TreeFoldPins
open AttackVectors.LeafDecode3 AttackVectors.LeafHashList AttackVectors.CommittedRoot
open AttackVectors.FoldMembership
open MerkleSpec

set_option maxHeartbeats 1000000

/-- **A COMMITTED WITNESS'S LEAF IS A MEMBER.**  If a leaf hashed in `σh` folds, in `SF`, to the published root
of a list that is the tree's leaf-hash list, then its abstract projection `⟨key, nk⟩` is in the represented leaf
set.

This is `habs` for one witness, on facts about that run: the leaf's preimage is cached in both states, the two
states agree on the leaf region's tail, the reference state hashed the tree's chain, and the fold accepted. -/
theorem witness_leaf_member
    {SF σtree σh : EVMState} {p leaf : UInt256} {r : UInt256}
    (z0 path : UInt256) (height : ℕ) (i : ℕ)
    {L : List UInt256}
    (hisz : i < UInt256.size)
    -- the leaf-hash side: the witness's own memory hypotheses, plus cache presence in both states
    (hpb : (σh.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σh.mload 64).val)
    (hP : p = σh.mload 64)
    (htail : ∀ x : UInt256, (σh.mload 64).val + 128 ≤ x.val →
      x.val < (σh.mload 64).val + 159 →
      Finmap.lookup x SF.machine_state.memory = Finmap.lookup x σh.machine_state.memory)
    (hcf : Finmap.lookup
      (leafInterval SF (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
        (σh.mload (leaf + 64))) SF.keccak_map = some r)
    (hch : Finmap.lookup
      (leafInterval SF (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
        (σh.mload (leaf + 64))) σh.keccak_map = some r)
    -- the tree side
    (hnw : p.val + 160 ≤ 2 ^ 256)
    (hLlen : L.length = (σtree.sload 1).val)
    (hL : ∀ j : ℕ, j < (σtree.sload 1).val →
      L.getD j z0 = lh3 SF p (decodeLeaf3 σtree (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hidx : i < (σtree.sload 1).val)
    (hCi : Cached SF p (decodeLeaf3 σtree (i : UInt256)))
    (hchain : ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1)))
    (haccept : (generated.AtomicFlowManager.AtomicFlowManager.foldRoot SF path height 0
        (i : UInt256)
        (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1).1
      = rootOf (hashOf SF) z0 L height) :
    (⟨σh.mload leaf, σh.mload (leaf + 64)⟩ : IMTAbstract.AbsLeaf)
      ∈ generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf σtree := by
  subst hP
  refine fold_accept_implies_member hnw z0 path height i
    (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1
    hisz hLlen hL hinv hinj hfuel hne hcap hidx hchain haccept
    (Lc := ⟨σh.mload leaf, σh.mload (leaf + 32), σh.mload (leaf + 64)⟩)
    ⟨r, hcf⟩ hCi ?_
  exact committed_leafhash_in_fold_state hpb hplow htail hcf hch

/-- **REJECTION FORM.**  A leaf whose projection is absent from the represented set cannot have its committed
hash folded to the tree's published root — by any path the witness might supply. -/
theorem witness_non_member_rejects
    {SF σtree σh : EVMState} {p leaf : UInt256} {r : UInt256}
    (z0 path : UInt256) (height : ℕ) (i : ℕ)
    {L : List UInt256}
    (hisz : i < UInt256.size)
    (hpb : (σh.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σh.mload 64).val)
    (hP : p = σh.mload 64)
    (htail : ∀ x : UInt256, (σh.mload 64).val + 128 ≤ x.val →
      x.val < (σh.mload 64).val + 159 →
      Finmap.lookup x SF.machine_state.memory = Finmap.lookup x σh.machine_state.memory)
    (hcf : Finmap.lookup
      (leafInterval SF (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
        (σh.mload (leaf + 64))) SF.keccak_map = some r)
    (hch : Finmap.lookup
      (leafInterval SF (σh.mload 64) (σh.mload leaf) (σh.mload (leaf + 32))
        (σh.mload (leaf + 64))) σh.keccak_map = some r)
    (hnw : p.val + 160 ≤ 2 ^ 256)
    (hLlen : L.length = (σtree.sload 1).val)
    (hL : ∀ j : ℕ, j < (σtree.sload 1).val →
      L.getD j z0 = lh3 SF p (decodeLeaf3 σtree (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hidx : i < (σtree.sload 1).val)
    (hCi : Cached SF p (decodeLeaf3 σtree (i : UInt256)))
    (hchain : ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1)))
    (hnot : (⟨σh.mload leaf, σh.mload (leaf + 64)⟩ : IMTAbstract.AbsLeaf)
      ∉ generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf σtree) :
    (generated.AtomicFlowManager.AtomicFlowManager.foldRoot SF path height 0 (i : UInt256)
        (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1).1
      ≠ rootOf (hashOf SF) z0 L height :=
  fun haccept => hnot (witness_leaf_member z0 path height i hisz hpb hplow hP htail hcf hch hnw
    hLlen hL hinv hinj hfuel hne hcap hidx hCi hchain haccept)

end AttackVectors.WitnessMember
