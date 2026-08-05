import specs.FoldForced
import specs.FoldFuel
import specs.FoldCacheInj

/-
  THE ROOT-DOWNWARD DESCENT — a forged path cannot reach a builder's root.

  Everything this needs was built over the preceding commits:

    FoldForced.foldRoot_top_args_forced   the top combine is forced onto the builder's arguments
    FoldRightPeel.foldRoot_succ_right     the top combine, exposed (the structural obstacle, resolved)
    FoldFresh.cacheInUsed_foldRoot        the freshness invariant at depth
    FoldFresh.foldRoot_builder_entry      the builder's cache entries, same key at depth
    FoldCacheInj.cacheInj_foldRoot        cache injectivity at depth
    FoldFuel.fuel_nonempty_at_depth       the range bound at depth

  so the recursion is now an ordinary induction, and this file runs it.

  The builder's chain is given abstractly: `V l` is its accumulator at level `l`, `S l` its sibling there,
  and `hchain` says the reference state caches the pair it combined — in the parity-selected order, at the
  SAME index the attacker claims.  The conclusion is that an attacker whose fold reaches `V k` must have
  started from the builder's leaf `V 0` AND read the builder's sibling at every level.

  The only cryptographic hypothesis is `CacheInj σ`: keccak is injective on the preimages it has hashed.
  Nothing is assumed about the attacker's path — not that its pairs were ever hashed, not that its siblings
  come from anywhere in particular.  Axiom-free.
-/

namespace Clear.FoldDescent

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakFuel
open Clear.FoldRightPeel Clear.FoldForced Clear.FoldFresh Clear.FoldFuel Clear.FoldCacheInj
open generated.AtomicFlowManager.AtomicFlowManager

/-- The builder's left argument at level `l`: its accumulator when the index bit is even, else its
sibling. -/
def bLeft (V S : ℕ → UInt256) (idx : UInt256) (l : ℕ) : UInt256 :=
  if Fin.land (idxAt idx l) 1 = 0 then V l else S l

/-- The builder's right argument at level `l`. -/
def bRight (V S : ℕ → UInt256) (idx : UInt256) (l : ℕ) : UInt256 :=
  if Fin.land (idxAt idx l) 1 = 0 then S l else V l

/-- **THE DESCENT.**  If a fold of `k` levels reaches the builder's level-`k` value, then its leaf was the
builder's leaf and it read the builder's sibling at every level.

`hchain` is what a builder run leaves behind: at each level it hashed its own pair, in the parity-selected
order, to the next value.  Nothing is assumed about the attacker's path. -/
theorem fold_descent (path : UInt256) (V S : ℕ → UInt256) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState),
      CacheInUsed σ → CacheInj σ → Fuel σ k →
      (∀ l, l < k →
        Finmap.lookup (accInterval σ (bLeft V S idx l) (bRight V S idx l)) σ.keccak_map
          = some (V (l + 1))) →
      (foldRoot σ path k i idx cur).1 = V k →
      cur = V 0 ∧ ∀ l, l < k → topSib path σ l i idx cur = S l := by
  intro k
  induction k with
  | zero =>
    intro i idx cur σ _ _ _ _ hout
    exact ⟨hout, fun l hl => absurd hl (by omega)⟩
  | succ k ih =>
    intro i idx cur σ hinv hinj hfuel hchain hout
    -- the top combine is forced onto the builder's level-`k` pair
    have hforced := foldRoot_top_args_forced path k i idx cur σ
      (cacheInUsed_foldRoot path k i idx cur σ hinv)
      (fuel_nonempty_at_depth path k i idx cur σ hfuel)
      (cacheInj_foldRoot path k i idx cur σ hinv hinj)
      (foldRoot_builder_entry path k i idx cur σ (hchain k (by omega)))
      hout
    -- either way the fold's level-`k` value is the builder's
    have hk : (foldRoot σ path k i idx cur).1 = V k ∧ topSib path σ k i idx cur = S k := by
      by_cases hpar : Fin.land (idxAt idx k) 1 = 0
      · obtain ⟨h1, h2⟩ := hforced.1 hpar
        unfold bLeft at h1
        unfold bRight at h2
        rw [if_pos hpar] at h1
        rw [if_pos hpar] at h2
        exact ⟨h1, h2⟩
      · obtain ⟨h1, h2⟩ := hforced.2 hpar
        unfold bLeft at h1
        unfold bRight at h2
        rw [if_neg hpar] at h1
        rw [if_neg hpar] at h2
        exact ⟨h2, h1⟩
    obtain ⟨hcur, hsib⟩ := ih i idx cur σ hinv hinj (hfuel.mono (by omega))
      (fun l hl => hchain l (by omega)) hk.1
    refine ⟨hcur, fun l hl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | rfl
    · exact hsib l h
    · exact hk.2

/-- **A FORGED PATH IS REJECTED.**  If the leaf differs from the builder's, no path whatsoever makes the
fold reach the builder's value — the attacker is free to choose every sibling. -/
theorem no_forged_fold (path : UInt256) (V S : ℕ → UInt256)
    (k : ℕ) (i idx cur : UInt256) (σ : EVMState)
    (hinv : CacheInUsed σ) (hinj : CacheInj σ) (hfuel : Fuel σ k)
    (hchain : ∀ l, l < k →
      Finmap.lookup (accInterval σ (bLeft V S idx l) (bRight V S idx l)) σ.keccak_map
        = some (V (l + 1)))
    (hne : cur ≠ V 0) :
    (foldRoot σ path k i idx cur).1 ≠ V k :=
  fun hout => hne (fold_descent path V S k i idx cur σ hinv hinj hfuel hchain hout).1

end Clear.FoldDescent
