import specs.AttackVectors.WitnessMember
import specs.AttackVectors.ConcreteBridge

/-
  DELIVERED-XOR-RECLAIMED WITH BOTH OBLIGATIONS DISCHARGED.

  `WitnessMember.gap_impossible_of_committedAtIn` discharges `habs` but still takes `GapSound` of the represented
  leaf set as a hypothesis.  That one has a supplier: `AttackVectors.ConcreteBridge` shows a `ConcreteLeafHistory`
  — a history evolving by the DEPLOYED insert path — induces an `IMTAbstract.Evolution`, and
  `IMTAbstract.evolution_sound` carries soundness forward from a sound start.

  Composing them leaves NEITHER of the two obligations the chain was originally conditional on:

    * the tree-builder invariant (`GapSound`) — from the history;
    * the abstraction obligation (`habs`) — from the fold's acceptance plus keccak cache injectivity.

  What remains are facts about the deployment: the history follows the deployed insert path, the start state is
  sound, the reference state hashed the tree's chain, and the witnesses are well-formed.  Axiom-free.
-/

namespace AttackVectors.NoDoubleSpend

open Clear Clear.KeccakFresh Clear.KeccakFuel Clear.KeccakDeterminism Clear.CachedHash
open Clear.LeafHashWindow Clear.TreeFoldPins
open AttackVectors.LeafDecode3 AttackVectors.WitnessMember
open MerkleSpec

set_option maxHeartbeats 1000000

/-- **NO DELIVERY-AND-RECLAIM, BOTH OBLIGATIONS DISCHARGED.**  For a tree history that follows the deployed
insert path from a sound start, a delivery witness and a reclaim witness for the same commit value cannot coexist
under one published root.

Neither `GapSound` nor `habs` is assumed: the first comes from the history, the second from the fold. The only
cryptographic hypothesis is `CacheInj SF` — keccak injective on the preimages the reference state has hashed. -/
theorem no_delivery_and_reclaim
    {SF : EVMState} {σ : ℕ → EVMState} (n : ℕ)
    {p₀ path R z0 : UInt256} {height : ℕ} {L : List UInt256}
    -- the tree-builder side: a real history from a sound start
    (hhist : ConcreteBridge.ConcreteLeafHistory σ)
    (h0 : IMTAbstract.SoundState
      (generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf (σ 0)))
    -- the root-binding side
    (hnw : p₀.val + 160 ≤ 2 ^ 256)
    (hLlen : L.length = ((σ n).sload 1).val)
    (hL : ∀ j : ℕ, j < ((σ n).sload 1).val →
      L.getD j z0 = lh3 SF p₀ (decodeLeaf3 (σ n) (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hR : R = rootOf (hashOf SF) z0 L height)
    (hchain : ∀ i : ℕ, ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1)))
    -- the two witnesses
    {value wk wnk nk₁ : UInt256} {i₁ i₂ : ℕ}
    (hmem : CommittedAtIn SF (σ n) p₀ path R height i₁ value nk₁)
    (hgapleaf : CommittedAtIn SF (σ n) p₀ path R height i₂ wk wnk)
    (hlow : wk < value)
    (hwin : wnk = 0 ∨ value < wnk) : False :=
  gap_impossible_of_committedAtIn
    (IMTAbstract.evolution_sound (ConcreteBridge.concreteHistory_isEvolution hhist) h0 n).1
    hnw hLlen hL hinv hinj hfuel hne hcap hR hchain hmem hgapleaf hlow hwin

/-- The genesis form: soundness at step `0` from the genesis leaf set rather than assumed. -/
theorem no_delivery_and_reclaim_from_genesis
    {SF : EVMState} {σ : ℕ → EVMState} (n : ℕ)
    {p₀ path R z0 : UInt256} {height : ℕ} {L : List UInt256}
    (hhist : ConcreteBridge.ConcreteLeafHistory σ)
    (hgen : generated.L2InteropCommitmentTree.L2InteropCommitmentTree.leafSetOf (σ 0)
      = ({⟨0, 0⟩} : Finset IMTAbstract.AbsLeaf))
    (hnw : p₀.val + 160 ≤ 2 ^ 256)
    (hLlen : L.length = ((σ n).sload 1).val)
    (hL : ∀ j : ℕ, j < ((σ n).sload 1).val →
      L.getD j z0 = lh3 SF p₀ (decodeLeaf3 (σ n) (j : UInt256)))
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (hR : R = rootOf (hashOf SF) z0 L height)
    (hchain : ∀ i : ℕ, ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (Clear.FoldDescent.bLeft (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l)
          (Clear.FoldDescent.bRight (treeV (hashOf SF) z0 L (i : UInt256))
            (treeS (hashOf SF) z0 L (i : UInt256)) (i : UInt256) l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L (i : UInt256) (l + 1)))
    {value wk wnk nk₁ : UInt256} {i₁ i₂ : ℕ}
    (hmem : CommittedAtIn SF (σ n) p₀ path R height i₁ value nk₁)
    (hgapleaf : CommittedAtIn SF (σ n) p₀ path R height i₂ wk wnk)
    (hlow : wk < value)
    (hwin : wnk = 0 ∨ value < wnk) : False :=
  no_delivery_and_reclaim n hhist (by rw [hgen]; exact IMTAbstract.genesis_soundState)
    hnw hLlen hL hinv hinj hfuel hne hcap hR hchain hmem hgapleaf hlow hwin

end AttackVectors.NoDoubleSpend
