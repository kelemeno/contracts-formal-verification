import specs.KeccakFresh
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  THE FOLD'S KECCAK INVARIANTS.

  `specs/ForgeryFresh.lean` gives the one-step forgery atom: a step producing a builder-cached value was
  forced onto the builder's arguments.  Applying it along a path needs its side conditions to survive the
  fold, so this file establishes them for the DEPLOYED `foldRoot`:

    * `CacheInUsed` — every cached value is marked used — holds throughout;
    * cache entries present at the start are still present at the end.

  Both are proved by induction over the fold's own recursion, each step being an `accOut`.  These are the
  facts a level-by-level concrete descent consumes, and without them the one-step atom cannot be chained.

  Axiom-free.
-/

namespace Clear.FoldFresh

open Clear Clear.KeccakDeterminism Clear.KeccakFresh EVMState
open generated.AtomicFlowManager.AtomicFlowManager

/-- **THE FRESHNESS INVARIANT SURVIVES THE FOLD.**  Every value in the keccak cache is marked used, at
every point of the deployed path fold. -/
theorem cacheInUsed_foldRoot (path : UInt256) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState),
      CacheInUsed σ → CacheInUsed (foldRoot σ path k i idx cur).2 := by
  intro k
  induction k with
  | zero => intro i idx cur σ hinv; exact hinv
  | succ k ih =>
    intro i idx cur σ hinv
    show CacheInUsed (foldRoot (if Fin.land idx 1 = 0
        then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
        else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
      path k (i + 1) (Fin.shiftRight idx 1) _).2
    refine ih (i + 1) (Fin.shiftRight idx 1) _ _ ?_
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar]; exact cacheInUsed_accOut hinv
    · rw [if_neg hpar]; exact cacheInUsed_accOut hinv

/-- **CACHE ENTRIES SURVIVE THE FOLD.**  Anything cached before the fold is still cached after it, with
the same value — so a builder's entries remain available to the argument at every level. -/
theorem foldRoot_lookup_mono (path : UInt256) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState) (I : List UInt256) (w : UInt256),
      Finmap.lookup I σ.keccak_map = some w →
        Finmap.lookup I (foldRoot σ path k i idx cur).2.keccak_map = some w := by
  intro k
  induction k with
  | zero => intro i idx cur σ I w h; exact h
  | succ k ih =>
    intro i idx cur σ I w h
    show Finmap.lookup I (foldRoot (if Fin.land idx 1 = 0
        then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
        else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
      path k (i + 1) (Fin.shiftRight idx 1) _).2.keccak_map = some w
    refine ih (i + 1) (Fin.shiftRight idx 1) _ _ I w ?_
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar]; exact accOut_lookup_mono h
    · rw [if_neg hpar]; exact accOut_lookup_mono h

/-- The fold does not touch memory above the scratch, at any depth — the frame that lets the sibling
array be read after arbitrarily many hash steps. -/
theorem foldRoot_mload_high (path : UInt256) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState) (a : UInt256),
      96 ≤ a.val → a.val + 32 ≤ 2 ^ 256 →
      (foldRoot σ path k i idx cur).2.mload a = σ.mload a := by
  intro k
  induction k with
  | zero => intro i idx cur σ a _ _; rfl
  | succ k ih =>
    intro i idx cur σ a ha hnw
    show (foldRoot (if Fin.land idx 1 = 0
        then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
        else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
      path k (i + 1) (Fin.shiftRight idx 1) _).2.mload a = σ.mload a
    rw [ih (i + 1) (Fin.shiftRight idx 1) _ _ a ha hnw]
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar]; exact accOut_mload_high ha hnw
    · rw [if_neg hpar]; exact accOut_mload_high ha hnw

end Clear.FoldFresh
