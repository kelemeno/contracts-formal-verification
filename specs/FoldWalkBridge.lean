import specs.MerkleSpec
import specs.FinBits
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  ROOT BINDING, PIECE (2) — the contract's fold IS the pure Merkle walk.

  `AttackVectors.RootBinding` factored root binding into three pieces and proved
  the abstract kernel (1) and the list/set kernel (3).  Piece (2) is the
  correspondence between the contract's path fold and `MerkleSpec.walkPure`:

      foldRoot σ path k i idx cur   (AtomicFlowManager/imt_path_user.lean)
      walkPure h sibs lvl k idx x   (MerkleSpec)

  The two agree structurally — same parity-driven orientation, same halving
  descent — but differ in three ways, each isolated as a hypothesis here:

  * INDEX REPRESENTATION.  `foldRoot` uses `Fin.land idx 1` / `Fin.shiftRight idx 1`
    where `walkPure` uses `idx % 2` / `idx / 2`.  Discharged by `specs/FinBits.lean`,
    which is why this file could not be written before it.
  * HASH PURITY (`hpure`).  `foldRoot` threads the EVM through `accOut`, so its
    hash is state-dependent; `walkPure`'s `h` is a fixed function.  The blueprint's
    R6 supplies this by pre-caching every pair, which makes `accOut` replay a
    cached value and hence behave as a function.
  * SIBLING STREAM (`hsib`).  `foldRoot` reads siblings from memory at
    `path + 32*i + 32`; `walkPure` takes them as a stream.  Equal as long as the
    path region is not rewritten during the fold, which it is not.

  Under those, the fold's VALUE is exactly the walk's.  Axiom-freedom is inherited
  from whatever discharges the hypotheses.
-/

namespace Clear.FoldWalkBridge

open Clear Clear.FinBits Clear.KeccakDeterminism MerkleSpec
open generated.AtomicFlowManager.AtomicFlowManager

/-- **THE FOLD IS THE WALK.**  With a pure pair-hash, a fixed sibling stream, and
no level-counter wraparound, the contract's `foldRoot` returns exactly
`MerkleSpec.walkPure`'s value. -/
theorem foldRoot_eq_walkPure
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256)
    (hpure : ∀ (σ' : EVMState) (a b : UInt256), (accOut σ' a b).1 = h a b)
    (hsib : ∀ (σ' : EVMState) (j : UInt256),
      σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState),
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur := by
  intro k
  induction k with
  | zero =>
    intro i idx cur σ _
    rfl
  | succ k ih =>
    intro i idx cur σ hb
    have h1 : ((1 : UInt256)).val = 1 := by decide
    have hsz : UInt256.size = 2 ^ 256 := by norm_num
    have hisucc : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt (by omega)
    show (foldRoot _ path k (i + 1) (Fin.shiftRight idx 1) _).1 = _
    have hbnd : (i + 1).val + k < 2 ^ 256 := by rw [hisucc]; omega
    refine Eq.trans (ih (i + 1) (Fin.shiftRight idx 1) _ _ hbnd) ?_
    simp only [walkPure_succ, hisucc, shiftRight_one_val]
    congr 1
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar, hsib σ i, hpure]
      have : idx.val % 2 = 0 := (land_one_eq_zero_iff idx).mp hpar
      rw [if_neg (by omega)]
    · rw [if_neg hpar, hsib σ i, hpure]
      have : idx.val % 2 = 1 := (land_one_ne_zero_iff idx).mp hpar
      rw [if_pos this]

/-! ## The composite: the contract's fold recomputes the whole-tree root

`foldRoot_eq_walkPure` gives fold = walk; `MerkleSpec.walkPure_update` (M-A) gives
walk = whole-tree root of the updated leaf list.  Chaining them closes root-binding
piece (2) end to end: the contract's path fold is the root of the tree with the leaf
written at `idx`. -/

/-- **THE CONTRACT'S FOLD IS THE UPDATED TREE'S ROOT.**  Under the same three
hypotheses as `foldRoot_eq_walkPure` (pure pair-hash, fixed sibling stream, no level
wraparound) plus M-A's requirements on the sibling stream, the fold started at level
`0` from index `idx` with accumulator `cur` returns exactly
`rootOf h z0 (leaves.set idx.val cur) height`.

Together with `AttackVectors.RootBinding.mem_of_rootOf_eq` — equal roots force equal
leaf lists — this is what lets a published root be read as a statement about the
tree's leaves rather than about a fold. -/
theorem foldRoot_eq_rootOf
    (h : Hash) (z0 : UInt256) (path : UInt256) (sibs : ℕ → UInt256)
    (hpure : ∀ (σ' : EVMState) (a b : UInt256), (accOut σ' a b).1 = h a b)
    (hsib : ∀ (σ' : EVMState) (j : UInt256),
      σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val)
    (leaves : List UInt256) (idx : UInt256) (cur : UInt256) (height : ℕ)
    (σ : EVMState)
    (hb : height < 2 ^ 256)
    (hidx : idx.val < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 (leaves.set idx.val cur) l).getD (sibIdx (idx.val / 2 ^ l))
        (zeros h z0 l)) :
    (foldRoot σ path height 0 idx cur).1
      = rootOf h z0 (leaves.set idx.val cur) height := by
  have h0 : ((0 : UInt256)).val = 0 := by decide
  rw [foldRoot_eq_walkPure h path sibs hpure hsib height 0 idx cur σ (by rw [h0]; omega)]
  rw [h0]
  exact walkPure_update h z0 sibs leaves idx.val cur height hidx hcap hsibs

end Clear.FoldWalkBridge
