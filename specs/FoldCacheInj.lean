import specs.KeccakFresh
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  CACHE INJECTIVITY ACROSS THE FOLD.

  `KeccakFresh.cacheInj_accOut` shows a hash step cannot break cache injectivity — the value a miss assigns
  is fresh, so it cannot collide with anything already cached.  Running that along the deployed fold means
  the descent states injectivity ONCE, at the fold's start, instead of re-imposing it at every depth.

  Axiom-free.
-/

namespace Clear.FoldCacheInj

open Clear Clear.KeccakDeterminism Clear.KeccakFresh EVMState
open generated.AtomicFlowManager.AtomicFlowManager

/-- **CACHE INJECTIVITY SURVIVES THE FOLD.** -/
theorem cacheInj_foldRoot (path : UInt256) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState),
      CacheInUsed σ → CacheInj σ → CacheInj (foldRoot σ path k i idx cur).2 := by
  intro k
  induction k with
  | zero => intro i idx cur σ _ hinj; exact hinj
  | succ k ih =>
    intro i idx cur σ hinv hinj
    show CacheInj (foldRoot (if Fin.land idx 1 = 0
        then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
        else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
      path k (i + 1) (Fin.shiftRight idx 1) _).2
    refine ih (i + 1) (Fin.shiftRight idx 1) _ _ ?_ ?_
    · by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar]; exact cacheInUsed_accOut hinv
      · rw [if_neg hpar]; exact cacheInUsed_accOut hinv
    · by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar]; exact cacheInj_accOut hinv hinj
      · rw [if_neg hpar]; exact cacheInj_accOut hinv hinj

end Clear.FoldCacheInj
