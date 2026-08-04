import specs.AttackVectors.ConcreteBridge

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

end AttackVectors.LeafDecode3
