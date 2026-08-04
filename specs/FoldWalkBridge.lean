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

/-! ## THE HYPOTHESES, WEAKENED TO AN INVARIANT

`foldRoot_eq_walkPure` quantifies `hpure` and `hsib` over ALL states.  Nothing can satisfy
that: `specs/CachedHash.lean` shows the node hash must be read off a keccak cache (Clear's
keccak is freshness-based, so no global pure function exists), and a cache-derived hash agrees
with `accOut` only where the entry is present — never universally.  The same over-strength
defeated the leaf hash until `LeafDecode3.root_binding_restricted` restricted injectivity to a
predicate.

The fix is the same shape, and here it is exact rather than merely sufficient: `foldRoot`
evolves its state ONLY by `accOut` (see its definition in `imt_path_user.lean`), so the
hypotheses are needed precisely on states reachable from the start by `accOut` steps.  Taking
an arbitrary predicate closed under one step captures that with no reachability machinery.

`KeccakDeterminism` already supplies the three closure facts an instantiation needs —
`accOut_junk_window` (the junk window survives a step), `accOut_lookup_mono` (cache entries
survive), `accOut_mload_high` (words above the scratch survive).  That is what makes a
concrete `Good` constructible.
-/

/-- **THE FOLD IS THE WALK, ON AN INVARIANT.**  As `foldRoot_eq_walkPure`, but the pure-hash
and fixed-sibling hypotheses are required only on states satisfying `Good`, which need only
hold at the start and be closed under one `accOut` step.

This is the form a cache-derived hash can instantiate. -/
theorem foldRoot_eq_walkPure_of_inv
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256) (Good : EVMState → Prop)
    (hclosed : ∀ (σ' : EVMState) (a b : UInt256), Good σ' → Good (accOut σ' a b).2)
    (hpure : ∀ (σ' : EVMState) (a b : UInt256), Good σ' → (accOut σ' a b).1 = h a b)
    (hsib : ∀ (σ' : EVMState) (j : UInt256), Good σ' →
      σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState), Good σ →
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur := by
  intro k
  induction k with
  | zero =>
    intro i idx cur σ _ _
    rfl
  | succ k ih =>
    intro i idx cur σ hg hb
    have h1 : ((1 : UInt256)).val = 1 := by decide
    have hsz : UInt256.size = 2 ^ 256 := by norm_num
    have hisucc : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt (by omega)
    show (foldRoot _ path k (i + 1) (Fin.shiftRight idx 1) _).1 = _
    have hbnd : (i + 1).val + k < 2 ^ 256 := by rw [hisucc]; omega
    -- the invariant survives this level's hash step, whichever orientation it takes
    have hg2 : Good (if Fin.land idx 1 = 0
        then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
        else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2 := by
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar]; exact hclosed σ _ _ hg
      · rw [if_neg hpar]; exact hclosed σ _ _ hg
    refine Eq.trans (ih (i + 1) (Fin.shiftRight idx 1) _ _ hg2 hbnd) ?_
    simp only [walkPure_succ, hisucc, shiftRight_one_val]
    congr 1
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar, hsib σ i hg, hpure _ _ _ hg]
      have : idx.val % 2 = 0 := (land_one_eq_zero_iff idx).mp hpar
      rw [if_neg (by omega)]
    · rw [if_neg hpar, hsib σ i hg, hpure _ _ _ hg]
      have : idx.val % 2 = 1 := (land_one_ne_zero_iff idx).mp hpar
      rw [if_pos this]

/-- The unrestricted `foldRoot_eq_walkPure` is the `Good := True` instance — recorded so the
weakening is visibly a generalization, not a parallel development. -/
theorem foldRoot_eq_walkPure_of_of_inv
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256)
    (hpure : ∀ (σ' : EVMState) (a b : UInt256), (accOut σ' a b).1 = h a b)
    (hsib : ∀ (σ' : EVMState) (j : UInt256),
      σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState),
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur :=
  fun k i idx cur σ hb =>
    foldRoot_eq_walkPure_of_inv h path sibs (fun _ => True)
      (fun _ _ _ _ => trivial) (fun σ' a b _ => hpure σ' a b)
      (fun σ' j _ => hsib σ' j) k i idx cur σ trivial hb

/-- **THE CONTRACT'S FOLD IS THE UPDATED TREE'S ROOT, ON AN INVARIANT.**  The composite of
`foldRoot_eq_walkPure_of_inv` with M-A, i.e. `foldRoot_eq_rootOf` with its two state-indexed
hypotheses restricted to a one-step-closed predicate.

This is the version root binding should be read through: its hash hypothesis is satisfiable
by a cache-derived hash, whereas `foldRoot_eq_rootOf`'s is not. -/
theorem foldRoot_eq_rootOf_of_inv
    (h : Hash) (z0 : UInt256) (path : UInt256) (sibs : ℕ → UInt256) (Good : EVMState → Prop)
    (hclosed : ∀ (σ' : EVMState) (a b : UInt256), Good σ' → Good (accOut σ' a b).2)
    (hpure : ∀ (σ' : EVMState) (a b : UInt256), Good σ' → (accOut σ' a b).1 = h a b)
    (hsib : ∀ (σ' : EVMState) (j : UInt256), Good σ' →
      σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val)
    (leaves : List UInt256) (idx : UInt256) (cur : UInt256) (height : ℕ)
    (σ : EVMState) (hg : Good σ)
    (hb : height < 2 ^ 256)
    (hidx : idx.val < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 (leaves.set idx.val cur) l).getD (sibIdx (idx.val / 2 ^ l))
        (zeros h z0 l)) :
    (foldRoot σ path height 0 idx cur).1
      = rootOf h z0 (leaves.set idx.val cur) height := by
  have h0 : ((0 : UInt256)).val = 0 := by decide
  rw [foldRoot_eq_walkPure_of_inv h path sibs Good hclosed hpure hsib height 0 idx cur σ hg
      (by rw [h0]; omega)]
  rw [h0]
  exact walkPure_update h z0 sibs leaves idx.val cur height hidx hcap hsibs

/-! ## THE INVARIANT, INDEXED BY LEVEL AND ACCUMULATOR

`foldRoot_eq_walkPure_of_inv` restricts the hypotheses to a predicate on STATES, which is
enough to make them satisfiable in principle but not in practice: its `hpure` still ranges
over ALL pairs `(a, b)`, so a concrete `Good` would have to assert that the reference state
caches every pair — and a real cache is finite.

The pairs the fold actually hashes are one per level: at level `i` with accumulator `cur` it
hashes `(cur, sibs i)` in one orientation or the other, and nothing else.  Indexing the
invariant by `(state, level, accumulator)` names exactly those, so a concrete instantiation
has a FINITE cache obligation — one entry per level of the path.

This is the last generalization needed; `hpure` below mentions only the two orientations of
the level's own pair.
-/

/-- **THE FOLD IS THE WALK, ON A LEVEL-INDEXED INVARIANT.**  The purity hypothesis is needed
only at the pair the level actually hashes, in the two orientations the parity bit selects.

`hclosed` carries the invariant to the next level with the step's post-state and output hash;
`hstep` is the same statement about the step's VALUE, split out so the closure obligation does
not have to re-derive the orientation. -/
theorem foldRoot_eq_walkPure_of_levelInv
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256)
    (Good : EVMState → UInt256 → UInt256 → Prop)
    (hsib : ∀ (σ' : EVMState) (i cur : UInt256), Good σ' i cur →
      σ'.mload ((path + Fin.shiftLeft i 5) + 32) = sibs i.val)
    (hpure : ∀ (σ' : EVMState) (i cur : UInt256), Good σ' i cur →
      (accOut σ' cur (sibs i.val)).1 = h cur (sibs i.val)
        ∧ (accOut σ' (sibs i.val) cur).1 = h (sibs i.val) cur)
    (hclosed : ∀ (σ' : EVMState) (i cur idx : UInt256), Good σ' i cur →
      Good (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).2
           (i + 1)
           (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).1) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState), Good σ i cur →
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur := by
  intro k
  induction k with
  | zero =>
    intro i idx cur σ _ _
    rfl
  | succ k ih =>
    intro i idx cur σ hg hb
    have h1 : ((1 : UInt256)).val = 1 := by decide
    have hsz : UInt256.size = 2 ^ 256 := by norm_num
    have hisucc : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hbnd : (i + 1).val + k < 2 ^ 256 := by rw [hisucc]; omega
    have hs := hsib σ i cur hg
    -- the level's sibling read is the stream's value, so the step is on the named pair
    show (foldRoot (if Fin.land idx 1 = 0
            then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
            else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
          path k (i + 1) (Fin.shiftRight idx 1)
          (if Fin.land idx 1 = 0
            then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
            else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).1).1 = _
    rw [hs]
    -- the level's output hash IS the walk's, so no congruence on `walkPure` is needed
    have hacc : (if Fin.land idx 1 = 0 then accOut σ cur (sibs i.val)
          else accOut σ (sibs i.val) cur).1
        = (if idx.val % 2 = 1 then h (sibs i.val) cur else h cur (sibs i.val)) := by
      obtain ⟨hp0, hp1⟩ := hpure σ i cur hg
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar, hp0]
        have : idx.val % 2 = 0 := (land_one_eq_zero_iff idx).mp hpar
        rw [if_neg (by omega)]
      · rw [if_neg hpar, hp1]
        have : idx.val % 2 = 1 := (land_one_ne_zero_iff idx).mp hpar
        rw [if_pos this]
    refine Eq.trans (ih (i + 1) (Fin.shiftRight idx 1) _ _ (hclosed σ i cur idx hg) hbnd) ?_
    simp only [walkPure_succ, hisucc, shiftRight_one_val, hacc]

/-- The state-only invariant version is the instance that ignores level and accumulator —
recorded so the finer form is visibly a generalization. -/
theorem foldRoot_eq_walkPure_of_inv_of_levelInv
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256) (Good : EVMState → Prop)
    (hclosed : ∀ (σ' : EVMState) (a b : UInt256), Good σ' → Good (accOut σ' a b).2)
    (hpure : ∀ (σ' : EVMState) (a b : UInt256), Good σ' → (accOut σ' a b).1 = h a b)
    (hsib : ∀ (σ' : EVMState) (j : UInt256), Good σ' →
      σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState), Good σ →
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur := by
  intro k i idx cur σ hg hb
  refine foldRoot_eq_walkPure_of_levelInv h path sibs (fun σ' _ _ => Good σ')
    (fun σ' j _ hgg => hsib σ' j hgg)
    (fun σ' i cur hgg => ⟨hpure σ' _ _ hgg, hpure σ' _ _ hgg⟩)
    (fun σ' i cur idx hgg => ?_) k i idx cur σ hg hb
  by_cases hpar : Fin.land idx 1 = 0
  · rw [if_pos hpar]; exact hclosed σ' _ _ hgg
  · rw [if_neg hpar]; exact hclosed σ' _ _ hgg

/-- **THE CONTRACT'S FOLD IS THE UPDATED TREE'S ROOT, ON A LEVEL-INDEXED INVARIANT.**  The
composite with M-A, on the weakest hypotheses in this file: purity is required only at the
pair each level hashes, so a concrete instantiation owes one cache entry per level. -/
theorem foldRoot_eq_rootOf_of_levelInv
    (h : Hash) (z0 : UInt256) (path : UInt256) (sibs : ℕ → UInt256)
    (Good : EVMState → UInt256 → UInt256 → Prop)
    (hsib : ∀ (σ' : EVMState) (i cur : UInt256), Good σ' i cur →
      σ'.mload ((path + Fin.shiftLeft i 5) + 32) = sibs i.val)
    (hpure : ∀ (σ' : EVMState) (i cur : UInt256), Good σ' i cur →
      (accOut σ' cur (sibs i.val)).1 = h cur (sibs i.val)
        ∧ (accOut σ' (sibs i.val) cur).1 = h (sibs i.val) cur)
    (hclosed : ∀ (σ' : EVMState) (i cur idx : UInt256), Good σ' i cur →
      Good (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).2
           (i + 1)
           (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).1)
    (leaves : List UInt256) (idx : UInt256) (cur : UInt256) (height : ℕ)
    (σ : EVMState) (hg : Good σ 0 cur)
    (hb : height < 2 ^ 256)
    (hidx : idx.val < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 (leaves.set idx.val cur) l).getD (sibIdx (idx.val / 2 ^ l))
        (zeros h z0 l)) :
    (foldRoot σ path height 0 idx cur).1
      = rootOf h z0 (leaves.set idx.val cur) height := by
  have h0 : ((0 : UInt256)).val = 0 := by decide
  rw [foldRoot_eq_walkPure_of_levelInv h path sibs Good hsib hpure hclosed height 0 idx cur σ hg
      (by rw [h0]; omega)]
  rw [h0]
  exact walkPure_update h z0 sibs leaves idx.val cur height hidx hcap hsibs

/-! ## THE INVARIANT, CARRYING THE INDEX TOO

`foldRoot_eq_walkPure_of_levelInv` made the cache obligation finite, but it is still not
instantiable, and the obstruction is precise: its `hclosed` quantifies `idx` UNIVERSALLY, so
the invariant must survive a step of EITHER parity.  A concrete `Good` would therefore have to
carry cache entries for both orientations at every level — and since each orientation leads to
a different accumulator, the set of accumulators it must cover doubles per level.  Finite, but
exponential in the path length, so useless.

The fix is to let the invariant see the index it is descending: closure is then required only
at the actual next index `idx >>> 1`, which pins the parity and so pins the accumulator.  A
concrete `Good` can then say "`cur` is the walk's own accumulator at this level, and the
reference state caches THAT pair" — one entry per level, no branching.

This is the weakest form in the file, and the one an instantiation should target. -/

/-- **THE FOLD IS THE WALK, ON A PATH INVARIANT.**  As `foldRoot_eq_walkPure_of_levelInv`, but
the invariant also carries the current index, so closure is required only at the next index the
fold actually descends to — pinning the parity, hence the accumulator. -/
theorem foldRoot_eq_walkPure_of_pathInv
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256)
    (Good : EVMState → UInt256 → UInt256 → UInt256 → Prop)
    (hsib : ∀ (σ' : EVMState) (i idx cur : UInt256), Good σ' i idx cur →
      σ'.mload ((path + Fin.shiftLeft i 5) + 32) = sibs i.val)
    (hpure : ∀ (σ' : EVMState) (i idx cur : UInt256), Good σ' i idx cur →
      (accOut σ' cur (sibs i.val)).1 = h cur (sibs i.val)
        ∧ (accOut σ' (sibs i.val) cur).1 = h (sibs i.val) cur)
    (hclosed : ∀ (σ' : EVMState) (i idx cur : UInt256), Good σ' i idx cur →
      Good (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).2
           (i + 1) (Fin.shiftRight idx 1)
           (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).1) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState), Good σ i idx cur →
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur := by
  intro k
  induction k with
  | zero =>
    intro i idx cur σ _ _
    rfl
  | succ k ih =>
    intro i idx cur σ hg hb
    have h1 : ((1 : UInt256)).val = 1 := by decide
    have hsz : UInt256.size = 2 ^ 256 := by norm_num
    have hisucc : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hbnd : (i + 1).val + k < 2 ^ 256 := by rw [hisucc]; omega
    have hs := hsib σ i idx cur hg
    show (foldRoot (if Fin.land idx 1 = 0
            then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
            else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).2
          path k (i + 1) (Fin.shiftRight idx 1)
          (if Fin.land idx 1 = 0
            then accOut σ cur (σ.mload ((path + Fin.shiftLeft i 5) + 32))
            else accOut σ (σ.mload ((path + Fin.shiftLeft i 5) + 32)) cur).1).1 = _
    rw [hs]
    have hacc : (if Fin.land idx 1 = 0 then accOut σ cur (sibs i.val)
          else accOut σ (sibs i.val) cur).1
        = (if idx.val % 2 = 1 then h (sibs i.val) cur else h cur (sibs i.val)) := by
      obtain ⟨hp0, hp1⟩ := hpure σ i idx cur hg
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar, hp0]
        have : idx.val % 2 = 0 := (land_one_eq_zero_iff idx).mp hpar
        rw [if_neg (by omega)]
      · rw [if_neg hpar, hp1]
        have : idx.val % 2 = 1 := (land_one_ne_zero_iff idx).mp hpar
        rw [if_pos this]
    refine Eq.trans (ih (i + 1) (Fin.shiftRight idx 1) _ _ (hclosed σ i idx cur hg) hbnd) ?_
    simp only [walkPure_succ, hisucc, shiftRight_one_val, hacc]

/-- The level-indexed version is the instance whose invariant ignores the index. -/
theorem foldRoot_eq_walkPure_of_levelInv_of_pathInv
    (h : Hash) (path : UInt256) (sibs : ℕ → UInt256)
    (Good : EVMState → UInt256 → UInt256 → Prop)
    (hsib : ∀ (σ' : EVMState) (i cur : UInt256), Good σ' i cur →
      σ'.mload ((path + Fin.shiftLeft i 5) + 32) = sibs i.val)
    (hpure : ∀ (σ' : EVMState) (i cur : UInt256), Good σ' i cur →
      (accOut σ' cur (sibs i.val)).1 = h cur (sibs i.val)
        ∧ (accOut σ' (sibs i.val) cur).1 = h (sibs i.val) cur)
    (hclosed : ∀ (σ' : EVMState) (i cur idx : UInt256), Good σ' i cur →
      Good (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).2
           (i + 1)
           (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).1) :
    ∀ (k : ℕ) (i idx cur : UInt256) (σ : EVMState), Good σ i cur →
      i.val + k < 2 ^ 256 →
      (foldRoot σ path k i idx cur).1 = walkPure h sibs i.val k idx.val cur :=
  fun k i idx cur σ hg hb =>
    foldRoot_eq_walkPure_of_pathInv h path sibs (fun σ' i _ cur => Good σ' i cur)
      (fun σ' i _ cur hgg => hsib σ' i cur hgg)
      (fun σ' i _ cur hgg => hpure σ' i cur hgg)
      (fun σ' i idx cur hgg => hclosed σ' i cur idx hgg)
      k i idx cur σ hg hb

/-- **THE CONTRACT'S FOLD IS THE UPDATED TREE'S ROOT, ON A PATH INVARIANT.**  The composite
with M-A on the weakest hypotheses available: purity at the level's own pair only, and closure
only along the index the fold descends. -/
theorem foldRoot_eq_rootOf_of_pathInv
    (h : Hash) (z0 : UInt256) (path : UInt256) (sibs : ℕ → UInt256)
    (Good : EVMState → UInt256 → UInt256 → UInt256 → Prop)
    (hsib : ∀ (σ' : EVMState) (i idx cur : UInt256), Good σ' i idx cur →
      σ'.mload ((path + Fin.shiftLeft i 5) + 32) = sibs i.val)
    (hpure : ∀ (σ' : EVMState) (i idx cur : UInt256), Good σ' i idx cur →
      (accOut σ' cur (sibs i.val)).1 = h cur (sibs i.val)
        ∧ (accOut σ' (sibs i.val) cur).1 = h (sibs i.val) cur)
    (hclosed : ∀ (σ' : EVMState) (i idx cur : UInt256), Good σ' i idx cur →
      Good (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).2
           (i + 1) (Fin.shiftRight idx 1)
           (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
              else accOut σ' (sibs i.val) cur).1)
    (leaves : List UInt256) (idx : UInt256) (cur : UInt256) (height : ℕ)
    (σ : EVMState) (hg : Good σ 0 idx cur)
    (hb : height < 2 ^ 256)
    (hidx : idx.val < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 (leaves.set idx.val cur) l).getD (sibIdx (idx.val / 2 ^ l))
        (zeros h z0 l)) :
    (foldRoot σ path height 0 idx cur).1
      = rootOf h z0 (leaves.set idx.val cur) height := by
  have h0 : ((0 : UInt256)).val = 0 := by decide
  rw [foldRoot_eq_walkPure_of_pathInv h path sibs Good hsib hpure hclosed height 0 idx cur σ hg
      (by rw [h0]; omega)]
  rw [h0]
  exact walkPure_update h z0 sibs leaves idx.val cur height hidx hcap hsibs

end Clear.FoldWalkBridge
