import specs.FoldRightPeel
import specs.FoldFresh
import specs.ForgeryFresh

/-
  THE FOLD'S TOP COMBINE IS FORCED.

  Three pieces are now in place:

    * `ForgeryFresh.accOut_args_forced` — a step producing a builder-cached value used the builder's
      arguments (freshness forces a hit, cache injectivity identifies the pair);
    * `FoldRightPeel.foldRoot_last_step_accOut` — the fold's last combine, exposed as a bare `accOut`;
    * `FoldFresh` — the keccak invariants, surviving the fold.

  This composes them: if a fold of `k + 1` levels produces a value the builder computed from `(c, d)`,
  then the fold's OWN top-level arguments are `(c, d)` — its reached accumulator and the sibling it read
  at the top level, in whichever order the parity bit selects.

  That is the induction step of a root-downward forgery argument, on the deployed fold, with no
  pair-injectivity-at-all-arguments anywhere.  The remaining work is the recursion itself, which now has
  no structural obstacle: `FoldFresh` re-establishes the hypotheses for the shorter fold.

  Axiom-free.
-/

namespace Clear.FoldForced

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.ForgeryFresh Clear.FoldRightPeel
open Clear.FoldFresh
open generated.AtomicFlowManager.AtomicFlowManager

/-- The sibling the fold reads at its top level. -/
def topSib (path : UInt256) (σ : EVMState) (k : ℕ) (i idx cur : UInt256) : UInt256 :=
  (foldRoot σ path k i idx cur).2.mload ((path + Fin.shiftLeft (lvlAt i k) 5) + 32)

/-- **THE TOP COMBINE IS FORCED.**  A fold of `k + 1` levels that produces a value the builder computed
from `(c, d)` must itself have combined `(c, d)` at its top level: the accumulator it reached and the
sibling it read there, ordered by the parity bit.

The cryptographic content is `hcinj` alone.  `hinv` and `hfuel` are the freshness side conditions, stated
at the state the first `k` levels produced — `FoldFresh.cacheInUsed_foldRoot` supplies `hinv` from the
fold's start state. -/
theorem foldRoot_top_args_forced (path : UInt256) (k : ℕ) (i idx cur : UInt256) (σ : EVMState)
    {c d v : UInt256}
    (hinv : CacheInUsed (foldRoot σ path k i idx cur).2)
    (hfuel : (List.partition
        (fun x => decide (x ∈ (foldRoot σ path k i idx cur).2.used_range))
        (foldRoot σ path k i idx cur).2.keccak_range).2 ≠ [])
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I (foldRoot σ path k i idx cur).2.keccak_map = some r →
        Finmap.lookup J (foldRoot σ path k i idx cur).2.keccak_map = some r → I = J)
    (hbuilder : Finmap.lookup
      (accInterval (foldRoot σ path k i idx cur).2 c d)
      (foldRoot σ path k i idx cur).2.keccak_map = some v)
    (hout : (foldRoot σ path (k + 1) i idx cur).1 = v) :
    (Fin.land (idxAt idx k) 1 = 0 →
        (foldRoot σ path k i idx cur).1 = c ∧ topSib path σ k i idx cur = d)
      ∧ (Fin.land (idxAt idx k) 1 ≠ 0 →
        topSib path σ k i idx cur = c ∧ (foldRoot σ path k i idx cur).1 = d) := by
  rw [foldRoot_last_step_accOut] at hout
  refine ⟨fun hpar => ?_, fun hpar => ?_⟩
  · rw [if_pos hpar] at hout
    exact accOut_args_forced hinv hfuel hcinj hbuilder hout
  · rw [if_neg hpar] at hout
    exact accOut_args_forced hinv hfuel hcinj hbuilder hout

/-- **NON-INCLUSION AT THE TOP.**  If neither orientation of the fold's reached accumulator and top
sibling is the builder's pair, the fold cannot produce the builder's value — for an arbitrary
attacker-chosen path, with nothing assumed about whether its pairs were ever hashed. -/
theorem foldRoot_top_ne (path : UInt256) (k : ℕ) (i idx cur : UInt256) (σ : EVMState)
    {c d v : UInt256}
    (hinv : CacheInUsed (foldRoot σ path k i idx cur).2)
    (hfuel : (List.partition
        (fun x => decide (x ∈ (foldRoot σ path k i idx cur).2.used_range))
        (foldRoot σ path k i idx cur).2.keccak_range).2 ≠ [])
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I (foldRoot σ path k i idx cur).2.keccak_map = some r →
        Finmap.lookup J (foldRoot σ path k i idx cur).2.keccak_map = some r → I = J)
    (hbuilder : Finmap.lookup
      (accInterval (foldRoot σ path k i idx cur).2 c d)
      (foldRoot σ path k i idx cur).2.keccak_map = some v)
    (heven : Fin.land (idxAt idx k) 1 = 0)
    (hne : ¬((foldRoot σ path k i idx cur).1 = c ∧ topSib path σ k i idx cur = d)) :
    (foldRoot σ path (k + 1) i idx cur).1 ≠ v :=
  fun hout => hne ((foldRoot_top_args_forced path k i idx cur σ hinv hfuel hcinj hbuilder hout).1 heven)

/-- The freshness invariant at the top state, from the fold's start state — so callers supply `hinv` once
at the beginning rather than at every depth. -/
theorem cacheInUsed_top (path : UInt256) (k : ℕ) (i idx cur : UInt256) (σ : EVMState)
    (hinv : CacheInUsed σ) : CacheInUsed (foldRoot σ path k i idx cur).2 :=
  cacheInUsed_foldRoot path k i idx cur σ hinv

end Clear.FoldForced
