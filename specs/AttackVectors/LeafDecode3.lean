import specs.AttackVectors.ConcreteBridge
import specs.AttackVectors.RootBinding
import specs.LeafHashWindow

/-
  THE THREE-FIELD LEAF DECODE — first step of root-binding piece (3).

  `AttackVectors.RootBinding` factored root binding into three pieces and proved the
  abstract kernels of (1) and (3).  Piece (3)'s CONCRETE instantiation is blocked on a
  modelling question the blueprint raises at §1.2 and §4.5:

      the contract's leaf hash covers ALL THREE fields of `IMTLeaf`
      (`value`, `nextIndex`, `nextValue`), while `IMTAbstract.AbsLeaf` deliberately
      drops `nextIndex`.

  So `leafSetOf` — an `AbsLeaf` set — cannot by itself determine what gets hashed into
  the tree, and no amount of Merkle reasoning closes that gap.  The blueprint's
  recommendation is to thread a three-field decode; this file introduces it and pins
  its relationship to the two-field one.

  Layout, verified against era-contracts at pin c67894b97
  (`l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol:21`):

      struct IMTLeaf { uint256 value; uint256 nextIndex; uint256 nextValue; }

  so the fields sit at `leafSlot σ i + 0/1/2` — the same `+0` and `+2` slots
  `decodeLeaf` already reads, plus the `+1` it ignores.

  WHAT THIS FILE DOES NOT DO.  It does not yet define `leafHashes`.  That needs the
  three fields laid out in MEMORY and hashed with `hashLeafOut`, which takes a memory
  pointer rather than storage — a separate construction.  This file only makes the
  abstraction gap explicit and shows the two decodes agree where they overlap, so the
  `nextIndex` component is the precisely identified missing information.
-/

namespace AttackVectors.LeafDecode3

open Clear IMTAbstract
open generated.L2InteropCommitmentTree.L2InteropCommitmentTree

/-- The full concrete leaf: all three `IMTLeaf` fields. -/
structure Leaf3 where
  value : UInt256
  nextIndex : UInt256
  nextValue : UInt256
deriving DecidableEq

/-- Forget `nextIndex`, landing in the abstract `AbsLeaf` the security layer uses. -/
def Leaf3.toAbs (L : Leaf3) : AbsLeaf := ⟨L.value, L.nextValue⟩

/-- Decode all three fields of the leaf at index `i` from storage. -/
def decodeLeaf3 (σ : EVMState) (i : UInt256) : Leaf3 :=
  ⟨σ.sload (leafSlot σ i), σ.sload (leafSlot σ i + 1), σ.sload (leafSlot σ i + 2)⟩

/-- **THE TWO DECODES AGREE WHERE THEY OVERLAP.**  Forgetting `nextIndex` from the
three-field decode gives exactly `decodeLeaf`, so the abstract security layer is
reading a genuine projection of the concrete leaf — not a different leaf. -/
theorem decodeLeaf3_toAbs (σ : EVMState) (i : UInt256) :
    (decodeLeaf3 σ i).toAbs = decodeLeaf σ i := rfl

/-- **THE MISSING COMPONENT, NAMED.**  Two leaves can share their abstract projection
and still differ — precisely when their `nextIndex` fields differ.  This is the
information the leaf hash covers and `leafSetOf` does not, so it is exactly what
piece (3) must supply to connect a published root to the abstract leaf set. -/
theorem toAbs_eq_iff (L M : Leaf3) :
    L.toAbs = M.toAbs ↔ L.value = M.value ∧ L.nextValue = M.nextValue := by
  constructor
  · intro h
    exact ⟨congrArg AbsLeaf.key h, congrArg AbsLeaf.nextKey h⟩
  · rintro ⟨h1, h2⟩
    unfold Leaf3.toAbs
    rw [h1, h2]

/-- Consequently the projection is injective exactly on leaves agreeing in
`nextIndex` — the sharp form of what the abstraction loses. -/
theorem toAbs_inj_of_nextIndex_eq {L M : Leaf3}
    (hni : L.nextIndex = M.nextIndex) (habs : L.toAbs = M.toAbs) : L = M := by
  obtain ⟨hv, hnv⟩ := (toAbs_eq_iff L M).mp habs
  cases L; cases M
  simp_all

/-! ## From a hashed leaf to set membership — piece (3), concrete

`MerkleSpec` parameterizes over the node hash rather than defining one, since the model
has no global pure keccak.  The leaf hash gets the same treatment: `lh` is any function
from a three-field leaf to a word — whatever the concrete layer supplies (`hashLeafOut`
composed with the memory layout) — and its INJECTIVITY is a hypothesis standing in for
leaf-hash collision resistance, exactly as node-hash pair-injectivity does for `h`.

The statements take the leaf's INDEX explicitly rather than quantifying over list
membership.  That is both easier to consume and closer to reality: a Merkle proof names
the index it opens, so a verifier always has it in hand. -/

/-- **PIECE (3), CONCRETE.**  If the leaf hash is injective and the leaf at index `i`
hashes to the same word as `L`, then `L`'s abstract projection is a member of the
represented leaf set.

This is the shape `AttackVectors.CrossContract`'s `habs` obligation needs: it converts
"the tree hashes this leaf at index `i`" into "this leaf is in `leafSetOf`".  With
`RootBinding.mem_of_rootOf_eq` (equal roots force equal leaf lists) it completes the
route from a published root to abstract set membership. -/
theorem mem_leafSetOf_of_hash_eq
    {lh : Leaf3 → UInt256} (hinj : ∀ L M : Leaf3, lh L = lh M → L = M)
    {σ : EVMState} {L : Leaf3} {i : ℕ}
    (hi : i < (σ.sload 1).val)
    (heq : lh (decodeLeaf3 σ (i : UInt256)) = lh L) :
    L.toAbs ∈ leafSetOf σ := by
  have hL : decodeLeaf3 σ (i : UInt256) = L := hinj _ _ heq
  unfold leafSetOf
  refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
  rw [← decodeLeaf3_toAbs σ (i : UInt256), hL]

/-- The contrapositive, which a NON-inclusion argument consumes: if a leaf's projection
is absent from the represented set, no in-range index hashes to it. -/
theorem hash_ne_of_not_mem_leafSetOf
    {lh : Leaf3 → UInt256} (hinj : ∀ L M : Leaf3, lh L = lh M → L = M)
    {σ : EVMState} {L : Leaf3} (hnot : L.toAbs ∉ leafSetOf σ)
    {i : ℕ} (hi : i < (σ.sload 1).val) :
    lh (decodeLeaf3 σ (i : UInt256)) ≠ lh L :=
  fun heq => hnot (mem_leafSetOf_of_hash_eq hinj hi heq)

/-! ## ROOT BINDING, COMPOSED

The three pieces meet.  Given

  * a leaf list that IS the tree's — characterized pointwise, so no list-valued
    definition and none of the coercion trouble that shape causes;
  * a CLAIMED list with the same published root;
  * a leaf `L` the claim places at index `i`;

the claimed list must equal the tree's (piece 1, `mem_of_rootOf_eq`'s engine), hence the
claim's entry at `i` is the tree's hash there (piece 3's premise), hence `L`'s projection
is in the represented leaf set (piece 3).

That is `habs` — the last obligation of `AttackVectors.CrossContract` — discharged, on
two named cryptographic hypotheses: node-hash pair-injectivity and leaf-hash
injectivity. -/

/-- **ROOT BINDING.**  A leaf placed at index `i` by any list carrying the tree's
published root really is a leaf of the represented set.

`hleaves` says the reference list is the tree's own leaf-hash list, stated pointwise.
`hroot` is the published-root agreement a verifier checks.  `hclaim` is what the
verifier's proof asserts at the opened index.  The conclusion is the abstract membership
the security layer reasons about.

Both cryptographic assumptions are explicit: `hnodeinj` (node-hash pair-injectivity,
standing in for keccak collision resistance in the tree) and `hinj` (the same for the
leaf hash).  Nothing else is assumed about either hash. -/
theorem root_binding
    {lh : Leaf3 → UInt256} (hinj : ∀ L M : Leaf3, lh L = lh M → L = M)
    {h : MerkleSpec.Hash} {z0 : UInt256}
    (hnodeinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {σ : EVMState} {height : ℕ}
    {leaves claimed : List UInt256}
    (hleaves : ∀ j : ℕ, j < (σ.sload 1).val →
      leaves.getD j 0 = lh (decodeLeaf3 σ (j : UInt256)))
    (hlen : claimed.length = leaves.length)
    (hcap : claimed.length ≤ 2 ^ height)
    (hroot : MerkleSpec.rootOf h z0 claimed height
      = MerkleSpec.rootOf h z0 leaves height)
    {L : Leaf3} {i : ℕ} (hi : i < (σ.sload 1).val)
    (hclaim : claimed.getD i 0 = lh L) :
    L.toAbs ∈ leafSetOf σ := by
  have hsame : claimed.getD i 0 = leaves.getD i 0 :=
    RootBinding.getD_of_rootOf_eq h z0 hnodeinj claimed leaves height hlen hcap hroot i 0
  refine mem_leafSetOf_of_hash_eq hinj hi ?_
  rw [← hleaves i hi, ← hsame, hclaim]

/-! ## RESTRICTED INJECTIVITY — what a cache-derived hash can actually supply

`root_binding` asks for `hinj` over ALL of `Leaf3`.  The contract's leaf hash cannot
satisfy that as modelled: `LeafHashWindow.leafHashOf` reads keccak off a state's cache, so
every UNCACHED leaf maps to `0` and injectivity fails vacuously on the tail.  That is a
property of the freshness-based keccak model, not a defect in the tree.

The fix costs nothing, because `hinj` is used at exactly TWO leaves — the decoded leaf at
the opened index and the claimed one.  So injectivity restricted to any predicate `P`
holding at those two is enough, and a cache-presence predicate is such a `P`.  The
unrestricted theorems above are the `P := fun _ => True` instances.
-/

/-- `mem_leafSetOf_of_hash_eq` with injectivity restricted to a predicate `P`. -/
theorem mem_leafSetOf_of_hash_eq_restricted
    {lh : Leaf3 → UInt256} {P : Leaf3 → Prop}
    (hinj : ∀ L M : Leaf3, P L → P M → lh L = lh M → L = M)
    {σ : EVMState} {L : Leaf3} {i : ℕ}
    (hi : i < (σ.sload 1).val)
    (hPi : P (decodeLeaf3 σ (i : UInt256))) (hPL : P L)
    (heq : lh (decodeLeaf3 σ (i : UInt256)) = lh L) :
    L.toAbs ∈ leafSetOf σ := by
  have hL : decodeLeaf3 σ (i : UInt256) = L := hinj _ _ hPi hPL heq
  unfold leafSetOf
  refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
  rw [← decodeLeaf3_toAbs σ (i : UInt256), hL]

/-- **ROOT BINDING, RESTRICTED.**  As `root_binding`, but the leaf hash need only be
injective on leaves satisfying `P`, and `P` need only hold at the two leaves the argument
touches: the tree's leaf at the opened index, and the claimed one.

This is the form the CONTRACT's hash can instantiate — see `root_binding_cached` below. -/
theorem root_binding_restricted
    {lh : Leaf3 → UInt256} {P : Leaf3 → Prop}
    (hinj : ∀ L M : Leaf3, P L → P M → lh L = lh M → L = M)
    {h : MerkleSpec.Hash} {z0 : UInt256}
    (hnodeinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {σ : EVMState} {height : ℕ}
    {leaves claimed : List UInt256}
    (hleaves : ∀ j : ℕ, j < (σ.sload 1).val →
      leaves.getD j 0 = lh (decodeLeaf3 σ (j : UInt256)))
    (hlen : claimed.length = leaves.length)
    (hcap : claimed.length ≤ 2 ^ height)
    (hroot : MerkleSpec.rootOf h z0 claimed height
      = MerkleSpec.rootOf h z0 leaves height)
    {L : Leaf3} {i : ℕ} (hi : i < (σ.sload 1).val)
    (hPi : P (decodeLeaf3 σ (i : UInt256))) (hPL : P L)
    (hclaim : claimed.getD i 0 = lh L) :
    L.toAbs ∈ leafSetOf σ := by
  have hsame : claimed.getD i 0 = leaves.getD i 0 :=
    RootBinding.getD_of_rootOf_eq h z0 hnodeinj claimed leaves height hlen hcap hroot i 0
  refine mem_leafSetOf_of_hash_eq_restricted hinj hi hPi hPL ?_
  rw [← hleaves i hi, ← hsame, hclaim]

/-- The unrestricted `root_binding` is the `P := True` instance — recorded so the
generalization is visibly a generalization, not a parallel development. -/
theorem root_binding_of_restricted
    {lh : Leaf3 → UInt256} (hinj : ∀ L M : Leaf3, lh L = lh M → L = M)
    {h : MerkleSpec.Hash} {z0 : UInt256}
    (hnodeinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {σ : EVMState} {height : ℕ}
    {leaves claimed : List UInt256}
    (hleaves : ∀ j : ℕ, j < (σ.sload 1).val →
      leaves.getD j 0 = lh (decodeLeaf3 σ (j : UInt256)))
    (hlen : claimed.length = leaves.length)
    (hcap : claimed.length ≤ 2 ^ height)
    (hroot : MerkleSpec.rootOf h z0 claimed height
      = MerkleSpec.rootOf h z0 leaves height)
    {L : Leaf3} {i : ℕ} (hi : i < (σ.sload 1).val)
    (hclaim : claimed.getD i 0 = lh L) :
    L.toAbs ∈ leafSetOf σ :=
  root_binding_restricted (P := fun _ => True) (fun L M _ _ he => hinj L M he)
    hnodeinj hleaves hlen hcap hroot hi trivial trivial hclaim

/-! ## THE CONTRACT'S LEAF HASH, PLUGGED IN

`lh3` is `LeafHashWindow.leafHashOf` viewed as a function on `Leaf3`, i.e. the hash
`fun_hashLeaf` computes when the leaf is laid out at pointer `p` in the reference state
`SF`.  `Cached` is the cache-presence predicate.  `lh3_inj_on_cached` is R7's `hinj`, and
`root_binding_cached` is root binding with NO abstract leaf hash left in it. -/

/-- The contract's leaf hash, as a function on `Leaf3`. -/
def lh3 (SF : EVMState) (p : UInt256) (L : Leaf3) : UInt256 :=
  Clear.LeafHashWindow.leafHashOf SF p L.value L.nextIndex L.nextValue

/-- The leaf's hash preimage is present in the reference state's keccak cache. -/
def Cached (SF : EVMState) (p : UInt256) (L : Leaf3) : Prop :=
  ∃ r : UInt256, Finmap.lookup
    (Clear.LeafHashWindow.leafInterval SF p L.value L.nextIndex L.nextValue)
    SF.keccak_map = some r

/-- **R7's `hinj`, for the CONTRACT's hash.**  On cached leaves, the deployed leaf hash is
injective — given keccak cache injectivity, the model-level form of collision resistance.
No assumption about an abstract `lh` remains. -/
theorem lh3_inj_on_cached
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J) :
    ∀ L M : Leaf3, Cached SF p L → Cached SF p M → lh3 SF p L = lh3 SF p M → L = M := by
  intro L M hL hM heq
  obtain ⟨hv, hni, hnv⟩ :=
    Clear.LeafHashWindow.leafHashOf_inj_of_eq hnw hcinj hL hM heq
  cases L; cases M
  simp_all

/-- **ROOT BINDING FOR THE DEPLOYED LEAF HASH.**  A leaf placed at index `i` by any list
carrying the tree's published root really is a leaf of the represented set — with the leaf
hash being the one `fun_hashLeaf` computes, not an abstract stand-in.

The remaining cryptographic hypotheses are exactly two, both stated at the model's own
granularity: node-hash pair-injectivity (`hnodeinj`) and keccak cache injectivity
(`hcinj`).  The cache-presence side conditions are discharged in a real run by the fact
that the tree HASHED both leaves — that is what put them in the cache. -/
theorem root_binding_cached
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    {h : MerkleSpec.Hash} {z0 : UInt256}
    (hnodeinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {σ : EVMState} {height : ℕ}
    {leaves claimed : List UInt256}
    (hleaves : ∀ j : ℕ, j < (σ.sload 1).val →
      leaves.getD j 0 = lh3 SF p (decodeLeaf3 σ (j : UInt256)))
    (hlen : claimed.length = leaves.length)
    (hcap : claimed.length ≤ 2 ^ height)
    (hroot : MerkleSpec.rootOf h z0 claimed height
      = MerkleSpec.rootOf h z0 leaves height)
    {L : Leaf3} {i : ℕ} (hi : i < (σ.sload 1).val)
    (hCi : Cached SF p (decodeLeaf3 σ (i : UInt256))) (hCL : Cached SF p L)
    (hclaim : claimed.getD i 0 = lh3 SF p L) :
    L.toAbs ∈ leafSetOf σ :=
  root_binding_restricted (P := Cached SF p) (lh3_inj_on_cached hnw hcinj)
    hnodeinj hleaves hlen hcap hroot hi hCi hCL hclaim

end AttackVectors.LeafDecode3
