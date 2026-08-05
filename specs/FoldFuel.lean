import specs.KeccakFuel
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  FUEL ACROSS THE FOLD — closing the `hfuel` threading problem.

  `specs/FoldForced.lean` applies the forgery atom at a depth, and its `hfuel` side condition has to hold
  THERE, not at the start.  `specs/KeccakFuel.lean` shows one step costs at most one unit.  This file runs
  that along the deployed fold: `k` levels cost at most `k` units, so a caller supplies a single fuel bound
  at the fold's start state and gets the side condition at every depth it needs.

  Axiom-free.
-/

namespace Clear.FoldFuel

open Clear Clear.KeccakDeterminism Clear.KeccakFuel EVMState
open generated.AtomicFlowManager.AtomicFlowManager

/-- **THE FOLD COSTS AT MOST ONE UNIT PER LEVEL.** -/
theorem fuel_foldRoot (path : UInt256) :
    ∀ (k n : ℕ) (i idx cur : UInt256) (σ : EVMState),
      Fuel σ (n + k) → Fuel (foldRoot σ path k i idx cur).2 n := by
  intro k
  induction k with
  | zero => intro n i idx cur σ h; simpa using h
  | succ k ih =>
    intro n i idx cur σ h
    show Fuel (foldRoot (if Fin.land idx 1 = 0
        then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
        else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
      path k (i + 1) (Fin.shiftRight idx 1) _).2 n
    refine ih n (i + 1) (Fin.shiftRight idx 1) _ _ ?_
    have h' : Fuel σ ((n + k) + 1) := h.mono (by omega)
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar]; exact Fuel.accOut h'
    · rw [if_neg hpar]; exact Fuel.accOut h'

/-- **THE SIDE CONDITION AT DEPTH.**  With `k + 1` levels' worth of fuel at the start, the state after `k`
levels still has an unused entry — exactly what `FoldForced.foldRoot_top_args_forced` requires.

So the full descent carries ONE fuel bound, at the fold's start, rather than an assumption re-imposed at
every depth. -/
theorem fuel_nonempty_at_depth (path : UInt256) (k : ℕ) (i idx cur : UInt256) (σ : EVMState)
    (h : Fuel σ (k + 1)) :
    (List.partition
        (fun x => decide (x ∈ (foldRoot σ path k i idx cur).2.used_range))
        (foldRoot σ path k i idx cur).2.keccak_range).2 ≠ [] :=
  Fuel.nonempty (n := 0) (fuel_foldRoot path k 1 i idx cur σ (by simpa [Nat.add_comm] using h))

end Clear.FoldFuel
