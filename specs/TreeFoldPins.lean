import specs.FoldDescent
import specs.FoldIndexBridge
import specs.MerkleSpec

/-
  THE DESCENT, INSTANTIATED FROM A REAL TREE.

  `FoldDescent.fold_descent` takes the builder's chain abstractly: `V l` its accumulator at level `l`, `S l`
  its sibling.  For a real tree those are the level-`l` nodes on and beside the path, so this file fills them
  in and states the consequence in the terms a verifier cares about:

      an attacker's fold that reaches the tree's published ROOT must have started from the tree's own LEAF
      at the opened index, and must have read the tree's own siblings at every level

  with the attacker free to choose every sibling, and only one cryptographic hypothesis — keccak injective on
  the preimages the reference state has hashed.

  This is the concrete analogue of `RootForgery.walk_accept_pins_leaf`, which assumed the siblings were
  honest, and of `MerkleProofSound.walk_accept_pins_leaf_free_sibs`, which did not but needed
  pair-injectivity at all arguments.  Axiom-free.
-/

namespace Clear.TreeFoldPins

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakFuel Clear.CachedHash
open Clear.FoldRightPeel Clear.FoldForced Clear.FoldDescent Clear.FoldIndexBridge
open MerkleSpec
open generated.AtomicFlowManager.AtomicFlowManager

/-- The tree's own accumulator at level `l` on the path to `idx`. -/
def treeV (h : Hash) (z0 : UInt256) (L : List UInt256) (idx : UInt256) (l : ℕ) : UInt256 :=
  (levels h z0 L l).getD (idx.val / 2 ^ l) (zeros h z0 l)

/-- The tree's own sibling at level `l` on that path. -/
def treeS (h : Hash) (z0 : UInt256) (L : List UInt256) (idx : UInt256) (l : ℕ) : UInt256 :=
  (levels h z0 L l).getD (sibIdx (idx.val / 2 ^ l)) (zeros h z0 l)

/-- At the leaf level the tree's accumulator is just the leaf. -/
theorem treeV_zero (h : Hash) (z0 : UInt256) (L : List UInt256) (idx : UInt256) :
    treeV h z0 L idx 0 = L.getD idx.val z0 := by
  unfold treeV
  rw [levels_zero, pow_zero, Nat.div_one, zeros_zero]

/-- At the top of a non-full tree the accumulator is the published root. -/
theorem treeV_height (h : Hash) (z0 : UInt256) (L : List UInt256) (idx : UInt256) (height : ℕ)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height) (hidx : idx.val < L.length) :
    treeV h z0 L idx height = rootOf h z0 L height := by
  unfold treeV
  rw [levels_height_singleton h z0 L height hne hcap,
      Nat.div_eq_of_lt (by omega)]
  rfl

/-- **THE DESCENT FROM A TREE.**  An attacker's fold reaching the tree's level-`k` node above `idx` must
have started from the tree's leaf at `idx` and read the tree's siblings throughout.

`hchain` is what a builder run leaves: at each level the reference state cached the pair it combined, in the
parity-selected order. -/
theorem tree_fold_pins_leaf {SF : EVMState} (z0 path : UInt256)
    (L : List UInt256) (k : ℕ) (i idx cur : UInt256)
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF k)
    (hchain : ∀ l, l < k →
      Finmap.lookup (accInterval SF
          (bLeft (treeV (hashOf SF) z0 L idx) (treeS (hashOf SF) z0 L idx) idx l)
          (bRight (treeV (hashOf SF) z0 L idx) (treeS (hashOf SF) z0 L idx) idx l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L idx (l + 1)))
    (hout : (foldRoot SF path k i idx cur).1 = treeV (hashOf SF) z0 L idx k) :
    cur = L.getD idx.val z0
      ∧ ∀ l, l < k → topSib path SF l i idx cur = treeS (hashOf SF) z0 L idx l := by
  obtain ⟨hleaf, hsib⟩ := fold_descent path (treeV (hashOf SF) z0 L idx)
    (treeS (hashOf SF) z0 L idx) k i idx cur SF hinv hinj hfuel hchain hout
  exact ⟨by rw [hleaf, treeV_zero], hsib⟩

/-- **AN ACCEPTED PROOF PINS THE LEAF — DEPLOYED FOLD, FREE SIBLINGS.**  If the contract's fold accepts a
claimed leaf against the tree's published root, the claim was the tree's own leaf at that index.

The attacker chooses the entire path array; nothing assumes its pairs were ever hashed. -/
theorem fold_accept_pins_leaf {SF : EVMState} (z0 path : UInt256)
    (L : List UInt256) (height : ℕ) (i idx cur : UInt256)
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height) (hidx : idx.val < L.length)
    (hchain : ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (bLeft (treeV (hashOf SF) z0 L idx) (treeS (hashOf SF) z0 L idx) idx l)
          (bRight (treeV (hashOf SF) z0 L idx) (treeS (hashOf SF) z0 L idx) idx l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L idx (l + 1)))
    (haccept : (foldRoot SF path height 0 idx cur).1 = rootOf (hashOf SF) z0 L height) :
    cur = L.getD idx.val z0 :=
  (tree_fold_pins_leaf z0 path L height 0 idx cur hinv hinj hfuel hchain
    (by rw [haccept, treeV_height _ z0 L idx height hne hcap hidx])).1

/-- **REJECTION.**  A claimed leaf differing from the tree's cannot be accepted against the tree's published
root, by any path whatsoever. -/
theorem fold_rejects_wrong_leaf {SF : EVMState} (z0 path : UInt256)
    (L : List UInt256) (height : ℕ) (i idx cur : UInt256)
    (hinv : CacheInUsed SF) (hinj : CacheInj SF) (hfuel : Fuel SF height)
    (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height) (hidx : idx.val < L.length)
    (hchain : ∀ l, l < height →
      Finmap.lookup (accInterval SF
          (bLeft (treeV (hashOf SF) z0 L idx) (treeS (hashOf SF) z0 L idx) idx l)
          (bRight (treeV (hashOf SF) z0 L idx) (treeS (hashOf SF) z0 L idx) idx l))
        SF.keccak_map = some (treeV (hashOf SF) z0 L idx (l + 1)))
    (hwrong : cur ≠ L.getD idx.val z0) :
    (foldRoot SF path height 0 idx cur).1 ≠ rootOf (hashOf SF) z0 L height :=
  fun haccept => hwrong (fold_accept_pins_leaf z0 path L height i idx cur hinv hinj hfuel
    hne hcap hidx hchain haccept)

end Clear.TreeFoldPins
