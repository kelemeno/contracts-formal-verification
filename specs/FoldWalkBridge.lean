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

end Clear.FoldWalkBridge
