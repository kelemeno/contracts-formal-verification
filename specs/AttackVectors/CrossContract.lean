import specs.AttackVectors.ConcreteBridge
import specs.AtomicFlowManager.AtomicFlowManager.exclusivity_user

/-
  THE CROSS-CONTRACT COMPOSITION.

  Two independently developed capstones meet here.

  On the AtomicFlowManager side, `committed_member_gap_impossible`
  (`exclusivity_user.lean`) proves DELIVERED-XOR-RECLAIMED for a published root
  `R`: a delivery witness (a committed leaf whose key is the commit value) and a
  reclaim witness (a committed adjacency leaf whose window straddles it) cannot
  coexist.  But it is conditional on

      hS : IMTAbstract.GapSound S

  for the set `S` that the committed leaves abstract into — described in that file
  as "the tree-builder invariant, the ONLY remaining obligation".

  On the L2InteropCommitmentTree side, that invariant is exactly what
  `AttackVectors.ConcreteBridge` establishes: a `ConcreteLeafHistory` from genesis
  induces an `IMTAbstract.Evolution`, and `evolution_sound` then gives
  `SoundState` — hence `GapSound` — at every snapshot.

  This file plugs the second into the first, so the AFM capstone no longer carries
  the tree-builder invariant as a hypothesis at all.

  ## What remains

  `habs` — that every leaf committed under the published root `R` really is a
  member of the represented leaf set — is NOT discharged here, and is not a
  bookkeeping gap.  It is ROOT BINDING: that a 32-byte root pins the leaf set that
  produced it.  That is the separate track (`MerkleSpec` M-D plus
  `AttackVectors.RootForgery`), and it rests on node-hash pair-injectivity as a
  cryptographic hypothesis.  So the honest reading of the theorem below is:

      GIVEN that the published root faithfully reflects the tree's leaves,
      no leg can be both delivered and reclaimed.

  and the "given" is the last real obligation in the chain, not a technicality.
-/

namespace AttackVectors.CrossContract

open Clear IMTAbstract
open generated.AtomicFlowManager.AtomicFlowManager

/-- **DELIVERED-XOR-RECLAIMED, with the tree-builder invariant DISCHARGED.**

The AtomicFlowManager exclusivity capstone, instantiated with the leaf set of a
real `L2InteropCommitmentTree` history: `GapSound` is no longer assumed but
supplied by `ConcreteBridge.concreteHistory_isEvolution` together with
`IMTAbstract.evolution_sound`.

So for a contract history from the genesis leaf set, a delivery witness and a
reclaim witness for the same commit value cannot coexist — provided the abstraction
hypothesis `habs` (root binding, see the file header) holds. -/
theorem committed_member_gap_impossible_of_history
    {σ : ℕ → EVMState} (n : ℕ)
    (hhist : ConcreteBridge.ConcreteLeafHistory σ)
    (hgen : generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf (σ 0)
      = ({⟨0, 0⟩} : Finset AbsLeaf))
    {R value wk wnk nk₁ : UInt256} {d : ℕ} {idx₁ idx₂ : UInt256}
    (habs : ∀ idx key nk, CommittedLeafAt R d idx key nk →
      (⟨key, nk⟩ : AbsLeaf) ∈
        generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf (σ n))
    (hmem : CommittedLeafAt R d idx₁ value nk₁)
    (hgapleaf : CommittedLeafAt R d idx₂ wk wnk)
    (hlow : wk < value)
    (hwin : wnk = 0 ∨ value < wnk) : False := by
  have h0 : SoundState
      (generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf (σ 0)) := by
    rw [hgen]; exact genesis_soundState
  have hevo := ConcreteBridge.concreteHistory_isEvolution hhist
  have hsound := evolution_sound hevo h0 n
  exact committed_member_gap_impossible hsound.1 habs hmem hgapleaf hlow hwin

end AttackVectors.CrossContract
