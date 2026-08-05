import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  RIGHT-PEELING THE FOLD — resolving the structural obstacle recorded in 4396f75.

  The concrete forgery argument runs from the ROOT DOWNWARD: the outermost combine must be a cache hit,
  which identifies its pair, and then one recurses.  But `foldRoot` recurses from the LEAF UPWARD, so the
  induction that peels its FIRST step is not the induction the argument wants.  4396f75 named two ways
  out and called the choice between them the next real decision.

  This is the first: a right-peeling form.  `foldRoot` over `k+1` levels is `k` levels followed by ONE
  more step, taken at the level, index and accumulator the fold has reached.  The state threads, which is
  why this is not a rewriting triviality — the last step runs in the state the first `k` produced, and
  that state has to be named.  Naming it as `(foldRoot σ path k i idx cur).2` makes the statement close by
  induction.

  The level and index sequences are given as iterates rather than arithmetic, which avoids `UInt256`
  wraparound side conditions entirely: the fold's own `i + 1` and `idx >>> 1` are applied literally.

  With this, a top-down argument becomes an ordinary induction on `k`.  Axiom-free.
-/

namespace Clear.FoldRightPeel

open Clear Clear.KeccakDeterminism
open generated.AtomicFlowManager.AtomicFlowManager

/-- One fold step: read the sibling for level `i`, combine in the parity-selected orientation. -/
def stepOnce (path : UInt256) (σ : EVMState) (i idx cur : UInt256) : UInt256 × EVMState :=
  if Fin.land idx 1 = 0
    then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
    else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur

/-- The level the fold has reached after `k` steps — the fold's own `i + 1`, iterated. -/
def lvlAt (i : UInt256) (k : ℕ) : UInt256 := (fun x => x + 1)^[k] i

/-- The index the fold has reached after `k` steps — the fold's own `idx >>> 1`, iterated. -/
def idxAt (idx : UInt256) (k : ℕ) : UInt256 := (fun x => Fin.shiftRight x 1)^[k] idx

@[simp] theorem lvlAt_zero (i : UInt256) : lvlAt i 0 = i := rfl

@[simp] theorem idxAt_zero (idx : UInt256) : idxAt idx 0 = idx := rfl

/-- Advancing the start by one step is the same as taking one more step — `Function.iterate_succ_apply`
in the form the fold produces. -/
theorem lvlAt_succ_start (i : UInt256) (k : ℕ) : lvlAt (i + 1) k = lvlAt i (k + 1) :=
  (Function.iterate_succ_apply _ k i).symm

theorem idxAt_succ_start (idx : UInt256) (k : ℕ) :
    idxAt (Fin.shiftRight idx 1) k = idxAt idx (k + 1) :=
  (Function.iterate_succ_apply _ k idx).symm

/-- The fold's first step, named. -/
private theorem foldRoot_succ_left (path : UInt256) (σ : EVMState) (k : ℕ) (i idx cur : UInt256) :
    foldRoot σ path (k + 1) i idx cur
      = foldRoot (stepOnce path σ i idx cur).2 path k (i + 1) (Fin.shiftRight idx 1)
          (stepOnce path σ i idx cur).1 := rfl

/-- **RIGHT-PEELING.**  `k + 1` fold levels are `k` levels followed by one more step, taken in the state
the first `k` produced and at the level, index and accumulator they reached.

This is the shape a root-downward argument inducts on: the LAST combine is exposed, so the fact that it
must be a cache hit (`ForgeryFresh.accOut_hit_of_output_cached`) can be applied at the root and the
induction continues into the shorter fold. -/
theorem foldRoot_succ_right (path : UInt256) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState),
      foldRoot σ path (k + 1) i idx cur
        = stepOnce path (foldRoot σ path k i idx cur).2
            (lvlAt i k) (idxAt idx k) (foldRoot σ path k i idx cur).1 := by
  intro k
  induction k with
  | zero =>
    intro i idx cur σ
    rw [foldRoot_succ_left]
    simp only [lvlAt_zero, idxAt_zero]
    rfl
  | succ k ih =>
    intro i idx cur σ
    rw [foldRoot_succ_left path σ (k + 1) i idx cur,
        ih (i + 1) (Fin.shiftRight idx 1) (stepOnce path σ i idx cur).1
          (stepOnce path σ i idx cur).2,
        lvlAt_succ_start, idxAt_succ_start,
        ← foldRoot_succ_left path σ k i idx cur]

/-- The fold's value at `k + 1` levels is the last step's value. -/
theorem foldRoot_succ_right_fst (path : UInt256) (k : ℕ) (i idx cur : UInt256) (σ : EVMState) :
    (foldRoot σ path (k + 1) i idx cur).1
      = (stepOnce path (foldRoot σ path k i idx cur).2
          (lvlAt i k) (idxAt idx k) (foldRoot σ path k i idx cur).1).1 := by
  rw [foldRoot_succ_right]

/-- The last step is an `accOut` on the fold's reached accumulator and the level's sibling, in one of the
two orientations — the form `ForgeryFresh.accOut_args_forced` applies to directly. -/
theorem foldRoot_last_step_accOut (path : UInt256) (k : ℕ) (i idx cur : UInt256) (σ : EVMState) :
    (foldRoot σ path (k + 1) i idx cur).1
      = (if Fin.land (idxAt idx k) 1 = 0
          then accOut (foldRoot σ path k i idx cur).2 (foldRoot σ path k i idx cur).1
            ((foldRoot σ path k i idx cur).2.mload
              ((path + Fin.shiftLeft (lvlAt i k) 5) + 32))
          else accOut (foldRoot σ path k i idx cur).2
            ((foldRoot σ path k i idx cur).2.mload
              ((path + Fin.shiftLeft (lvlAt i k) 5) + 32))
            (foldRoot σ path k i idx cur).1).1 := by
  rw [foldRoot_succ_right_fst]
  rfl

end Clear.FoldRightPeel
