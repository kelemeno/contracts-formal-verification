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

/-! ## THE ∀-FORM, ADDITIVELY

`committed_member_gap_impossible` wants `habs` quantified over witnesses.  `CommittedLeafAt` cannot support that
— it existentially quantifies the fold's STATE as well as its starting level, so `hashOf σf` varies per witness
while the published root is fixed.  Rather than redefine a predicate the AFM spec owns, `CommittedAtIn` below is
a NEW predicate that pins the reference state and level `0`, carries the run-level facts, and IMPLIES
`CommittedLeafAt`.  Nothing existing changes, and a capstone conditional on the weaker hypothesis still applies.

The per-witness free-memory pointer is reconciled with a canonical `p₀` by
`LeafHashWindow.leafHashOut_eq_leafHashOf_shift`, which is why that lemma exists. -/

/-- A committed leaf whose fold runs in a fixed reference state `SF` from level `0`, whose leaf hash is
reconciled to the canonical pointer `p₀`, together with the run-level facts making it well-formed. -/
def CommittedAtIn (SF σtree : EVMState) (p₀ path R : UInt256) (d i : ℕ) (key nk : UInt256) : Prop :=
  ∃ (σh : EVMState) (leaf r : UInt256),
    i < UInt256.size ∧
    i < (σtree.sload 1).val ∧
    (σh.mload 64).val + 128 ≤ 18446744073709551615 ∧
    96 ≤ (σh.mload 64).val ∧
    (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).2.hash_collision = false ∧
    (generated.AtomicFlowManager.AtomicFlowManager.foldRoot SF path d 0 (i : UInt256)
      (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1).2.hash_collision = false ∧
    (∀ x : ℕ, 128 ≤ x → x < 159 →
      Finmap.lookup (p₀ + (x : UInt256)) SF.machine_state.memory
        = Finmap.lookup ((σh.mload 64) + (x : UInt256)) σh.machine_state.memory) ∧
    Finmap.lookup (leafInterval SF p₀ (σh.mload leaf) (σh.mload (leaf + 32))
      (σh.mload (leaf + 64))) SF.keccak_map = some r ∧
    Finmap.lookup (leafInterval SF p₀ (σh.mload leaf) (σh.mload (leaf + 32))
      (σh.mload (leaf + 64))) σh.keccak_map = some r ∧
    Cached SF p₀ (decodeLeaf3 σtree (i : UInt256)) ∧
    (generated.AtomicFlowManager.AtomicFlowManager.foldRoot SF path d 0 (i : UInt256)
      (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1).1 = R ∧
    σh.mload leaf = key ∧ σh.mload (leaf + 64) = nk

/-- **THE PINNED FORM IMPLIES THE SPEC'S.**  So any result conditional on `habs` for `CommittedLeafAt` applies
once `habs` holds for well-formed witnesses — nothing the AFM spec states is weakened. -/
theorem committedLeafAt_of_committedAtIn {SF σtree : EVMState} {p₀ path R : UInt256} {d i : ℕ}
    {key nk : UInt256}
    (h : CommittedAtIn SF σtree p₀ path R d i key nk) :
    generated.AtomicFlowManager.AtomicFlowManager.CommittedLeafAt R d (i : UInt256) key nk := by
  obtain ⟨σh, leaf, r, -, -, hpb, hplow, hhc, hfc, -, -, -, -, hfold, hkey, hnk⟩ := h
  exact ⟨σh, leaf, SF, path, 0, hhc, hpb, hplow, hfc, hfold, hkey, hnk⟩

/-- A committed leaf's hash at the CANONICAL pointer — the pointer-reconciled form of
`CommittedRoot.committed_leafhash_in_fold_state`. -/
theorem committed_leafhash_at_pointer {SF σh : EVMState} {leaf p₀ r : UInt256}
    (hpb : (σh.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (σh.mload 64).val)
    (hp₀ : p₀.val + 160 ≤ 2 ^ 256)
    (htail : ∀ x : ℕ, 128 ≤ x → x < 159 →
      Finmap.lookup (p₀ + (x : UInt256)) SF.machine_state.memory
        = Finmap.lookup ((σh.mload 64) + (x : UInt256)) σh.machine_state.memory)
    (hcf : Finmap.lookup (leafInterval SF p₀ (σh.mload leaf) (σh.mload (leaf + 32))
      (σh.mload (leaf + 64))) SF.keccak_map = some r)
    (hch : Finmap.lookup (leafInterval SF p₀ (σh.mload leaf) (σh.mload (leaf + 32))
      (σh.mload (leaf + 64))) σh.keccak_map = some r) :
    (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1
      = leafHashOf SF p₀ (σh.mload leaf) (σh.mload (leaf + 32)) (σh.mload (leaf + 64)) := by
  rw [committed_leafhash_modelled hpb hplow]
  exact leafHashOut_eq_leafHashOf_shift hp₀ (by omega) htail hcf hch

/-- **`habs`, QUANTIFIED.**  Every well-formed committed witness's leaf is a member of the represented leaf set.

The tree-side hypotheses are shared across witnesses; each witness carries its own run-level facts inside
`CommittedAtIn`. -/
theorem habs_of_committedAtIn
    {SF σtree : EVMState} {p₀ path R z0 : UInt256} {height : ℕ} {L : List UInt256}
    (hnw : p₀.val + 160 ≤ 2 ^ 256)
    (hLlen : L.length = (σtree.sload 1).val)
    (hL : ∀ j : ℕ, j < (σtree.sload 1).val →
      L.getD j z0 = lh3 SF p₀ (decodeLeaf3 σtree (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hR : R = rootOf (hashOf SF) z0 L height)
    (hchain : ∀ i : ℕ, ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1))) :
    ∀ (i : ℕ) (key nk : UInt256), CommittedAtIn SF σtree p₀ path R height i key nk →
      (⟨key, nk⟩ : IMTAbstract.AbsLeaf)
        ∈ generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf σtree := by
  intro i key nk h
  obtain ⟨σh, leaf, r, hisz, hidx, hpb, hplow, -, -, htail, hcf, hch, hCi, hfold, hkey, hnk⟩ := h
  subst hkey; subst hnk
  refine fold_accept_implies_member hnw z0 path height i
    (generated.AtomicFlowManager.AtomicFlowManager.hashLeafOut σh leaf).1
    hisz hLlen hL hinv hinj hfuel hne hcap hidx (hchain i) (by rw [hfold, hR])
    (Lc := ⟨σh.mload leaf, σh.mload (leaf + 32), σh.mload (leaf + 64)⟩)
    ⟨r, hcf⟩ hCi ?_
  exact committed_leafhash_at_pointer hpb hplow hnw htail hcf hch

end AttackVectors.WitnessMember
