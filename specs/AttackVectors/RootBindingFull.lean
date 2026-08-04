import specs.AttackVectors.LeafDecode3
import specs.RootBindingCached

/-
  ROOT BINDING WITH BOTH HASHES DEPLOYED, AND ONE CRYPTOGRAPHIC HYPOTHESIS.

  The pieces now exist separately:

    * `LeafDecode3.root_binding_cached` — root binding with the deployed LEAF hash, but still
      taking node-hash pair-injectivity at all arguments as `hnodeinj`;
    * `RootBindingCached.getD_of_rootOf_eq_cached` — M-D for the deployed NODE hash, on the pairs
      the tree actually hashes.

  This file composes them.  The result takes NO abstract hash and exactly ONE cryptographic
  hypothesis — keccak cache injectivity — which serves both hashes at once, since
  `LeafHashWindow.leafInterval_inj` and `CachedHashInj.accInterval_inj` reduce leaf-hash and
  node-hash injectivity to that same statement.

  Everything else in the statement is a fact about the RUN: which preimages the reference state
  hashed (linear in the tree size), the published-root agreement a verifier checks, and the
  leaf-list characterization.  Axiom-free.
-/

namespace AttackVectors.RootBindingFull

open Clear Clear.CachedHash Clear.MerkleCachedInj Clear.RootBindingCached
open AttackVectors.LeafDecode3
open generated.L2InteropCommitmentTree.L2InteropCommitmentTree

/-- **ROOT BINDING, FULLY DEPLOYED.**  A leaf placed at index `i` by any list carrying the tree's
published root really is a leaf of the represented set — with the leaf hash being the one
`fun_hashLeaf` computes, the node hash the one the accessor computes, and one cryptographic
hypothesis for both.

The hypotheses, all checkable of a run:
* `hcinj` — keccak is injective on the preimages the reference state has hashed.  THE ONLY
  cryptographic idealization; it discharges leaf-hash injectivity (via `leafInterval_inj`) and
  node-hash pair-injectivity (via `accInterval_inj`) simultaneously.
* `hp₁` / `hp₂` — the reference state hashed every adjacent pair of every level of both lists.
* `hCi` / `hCL` — it hashed the two leaves' own preimages.
* `hleaves` — the reference list is the tree's leaf-hash list, stated pointwise.
* `hroot` — the published-root agreement a verifier checks.
* `hnw`, `hlen`, `hne`, `hcap` — layout and width side conditions. -/
theorem root_binding_fully_cached
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    (z0 : UInt256)
    {σ : EVMState} {height : ℕ} {leaves claimed : List UInt256}
    (hleaves : ∀ j : ℕ, j < (σ.sload 1).val →
      leaves.getD j 0 = lh3 SF p (decodeLeaf3 σ (j : UInt256)))
    (hlen : claimed.length = leaves.length) (hne : claimed.length ≠ 0)
    (hcap : claimed.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height,
      PairsOK (CachedPair SF) (MerkleSpec.zeros (hashOf SF) z0 l)
        (MerkleSpec.levels (hashOf SF) z0 claimed l))
    (hp₂ : ∀ l < height,
      PairsOK (CachedPair SF) (MerkleSpec.zeros (hashOf SF) z0 l)
        (MerkleSpec.levels (hashOf SF) z0 leaves l))
    (hroot : MerkleSpec.rootOf (hashOf SF) z0 claimed height
      = MerkleSpec.rootOf (hashOf SF) z0 leaves height)
    {L : Leaf3} {i : ℕ} (hi : i < (σ.sload 1).val)
    (hCi : Cached SF p (decodeLeaf3 σ (i : UInt256))) (hCL : Cached SF p L)
    (hclaim : claimed.getD i 0 = lh3 SF p L) :
    L.toAbs ∈ leafSetOf σ := by
  have hsame : claimed.getD i 0 = leaves.getD i 0 :=
    getD_of_rootOf_eq_cached z0 hcinj claimed leaves height hlen hne hcap hp₁ hp₂ hroot i 0
  refine mem_leafSetOf_of_hash_eq_restricted (lh3_inj_on_cached hnw hcinj) hi hCi hCL ?_
  rw [← hleaves i hi, ← hsame, hclaim]

/-- The non-inclusion direction, which an attack argument consumes: if a leaf's abstract
projection is absent from the represented set, no list carrying the tree's published root can
place it at an in-range index.

This is the shape a forged-membership attack has to defeat, and it defeats it only by breaking
`hcinj`. -/
theorem not_placeable_of_not_mem
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    (z0 : UInt256)
    {σ : EVMState} {height : ℕ} {leaves claimed : List UInt256}
    (hleaves : ∀ j : ℕ, j < (σ.sload 1).val →
      leaves.getD j 0 = lh3 SF p (decodeLeaf3 σ (j : UInt256)))
    (hlen : claimed.length = leaves.length) (hne : claimed.length ≠ 0)
    (hcap : claimed.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height,
      PairsOK (CachedPair SF) (MerkleSpec.zeros (hashOf SF) z0 l)
        (MerkleSpec.levels (hashOf SF) z0 claimed l))
    (hp₂ : ∀ l < height,
      PairsOK (CachedPair SF) (MerkleSpec.zeros (hashOf SF) z0 l)
        (MerkleSpec.levels (hashOf SF) z0 leaves l))
    (hroot : MerkleSpec.rootOf (hashOf SF) z0 claimed height
      = MerkleSpec.rootOf (hashOf SF) z0 leaves height)
    {L : Leaf3} (hnot : L.toAbs ∉ leafSetOf σ)
    {i : ℕ} (hi : i < (σ.sload 1).val)
    (hCi : Cached SF p (decodeLeaf3 σ (i : UInt256))) (hCL : Cached SF p L) :
    claimed.getD i 0 ≠ lh3 SF p L :=
  fun hclaim => hnot (root_binding_fully_cached hnw hcinj z0 hleaves hlen hne hcap hp₁ hp₂ hroot
    hi hCi hCL hclaim)

end AttackVectors.RootBindingFull
