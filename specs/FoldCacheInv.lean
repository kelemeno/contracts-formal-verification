import specs.FoldWalkBridge
import specs.CachedHash

/-
  THE CONCRETE FOLD INVARIANT — no unsatisfiable hypothesis left.

  `specs/FoldWalkBridge.lean` weakened the fold correspondence four times, ending at
  `foldRoot_eq_walkPure_of_stepInv`, whose invariant ranges over `foldRoot`'s own recursion
  state `(σ, i, idx, cur, k)`.  Each weakening was forced by an obstruction to instantiating
  its predecessor.  This file finally instantiates it.

  `CacheInv` says, at a fold state:

    * the level and remaining steps add up to the path length;
    * the index is the start index descended `i` times;
    * the accumulator is the WALK's own accumulator at this level (`accAt`, a pure recursion);
    * memory agrees with a reference state `SF` on the keccak junk window `[64, 95)`;
    * `SF` caches both orientations of every pair the walk hashes, and this state still
      carries those entries;
    * the sibling array reads back the stream, up to the path length.

  All four obligations of `foldRoot_eq_walkPure_of_stepInv` are then discharged from lemmas
  that already existed for exactly this purpose: `CachedHash.accOut_eq_hashOf` for purity,
  and `accOut_junk_window` / `accOut_lookup_mono` / `accOut_mload_high` for closure.

  The hash is `CachedHash.hashOf SF` — read off `SF`'s cache, because Clear's keccak is
  freshness-based and no global pure keccak exists.  The cache obligation is two entries per
  level: finite, and exactly what a builder run establishes by having hashed its own walk.

  Axiom-free.
-/

namespace Clear.FoldCacheInv

open Clear Clear.FinBits Clear.KeccakDeterminism Clear.CachedHash Clear.FoldWalkBridge
open MerkleSpec
open generated.AtomicFlowManager.AtomicFlowManager

set_option maxHeartbeats 1000000

/-- **THE WALK'S OWN ACCUMULATOR.**  The value the pure walk holds after folding `l` levels
from index `idx0` and leaf hash `cur0`.  A pure recursion — no state, no cache. -/
def accAt (h : Hash) (sibs : ℕ → UInt256) (idx0 : ℕ) (cur0 : UInt256) : ℕ → UInt256
  | 0 => cur0
  | (l + 1) =>
      if (idx0 / 2 ^ l) % 2 = 1
        then h (sibs l) (accAt h sibs idx0 cur0 l)
        else h (accAt h sibs idx0 cur0 l) (sibs l)

/-- The sibling slot's address value, given the array sits above the scratch and does not
wrap.  Uses the stride bridge `FinBits.shiftLeft_five_val`. -/
private lemma sib_addr_val {path j : UInt256} {height : ℕ}
    (hb : path.val + 32 * height + 32 < UInt256.size) (hj : j.val ≤ height) :
    ((path + Fin.shiftLeft j 5) + 32).val = path.val + 32 * j.val + 32 := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h32 : ((32 : UInt256)).val = 32 := by decide
  have hsl : (Fin.shiftLeft j 5).val = 32 * j.val :=
    shiftLeft_five_val j (by omega)
  have e1 : (path + Fin.shiftLeft j 5).val = path.val + 32 * j.val := by
    have : (path + Fin.shiftLeft j 5).val
        = (path.val + (Fin.shiftLeft j 5).val) % UInt256.size := rfl
    rw [this, hsl, Nat.mod_eq_of_lt (by omega)]
  have : ((path + Fin.shiftLeft j 5) + 32).val
      = ((path + Fin.shiftLeft j 5).val + ((32 : UInt256)).val) % UInt256.size := rfl
  rw [this, e1, h32, Nat.mod_eq_of_lt (by omega)]

/-- **THE CONCRETE FOLD INVARIANT.** -/
def CacheInv (SF : EVMState) (path : UInt256) (sibs : ℕ → UInt256)
    (idx0 cur0 : UInt256) (height : ℕ) :
    EVMState → UInt256 → UInt256 → UInt256 → ℕ → Prop :=
  fun σ' i idx cur k =>
      i.val + k = height
    ∧ idx.val = idx0.val / 2 ^ i.val
    ∧ cur = accAt (hashOf SF) sibs idx0.val cur0 i.val
    ∧ (∀ a : UInt256, 64 ≤ a.val → a.val ≤ 94 →
        Finmap.lookup a SF.machine_state.memory = Finmap.lookup a σ'.machine_state.memory)
    ∧ (∀ l : ℕ, l < height →
        (∃ r : UInt256,
          Finmap.lookup (accInterval SF (accAt (hashOf SF) sibs idx0.val cur0 l) (sibs l))
            SF.keccak_map = some r
          ∧ Finmap.lookup (accInterval SF (accAt (hashOf SF) sibs idx0.val cur0 l) (sibs l))
            σ'.keccak_map = some r)
        ∧ (∃ r : UInt256,
          Finmap.lookup (accInterval SF (sibs l) (accAt (hashOf SF) sibs idx0.val cur0 l))
            SF.keccak_map = some r
          ∧ Finmap.lookup (accInterval SF (sibs l) (accAt (hashOf SF) sibs idx0.val cur0 l))
            σ'.keccak_map = some r))
    ∧ (∀ j : UInt256, j.val ≤ height →
        σ'.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val)

/-- **PURITY, DISCHARGED.**  On the invariant, the level's hash step behaves as the fixed
function `hashOf SF` in both orientations — because `SF` caches that pair and this state
still carries the entry. -/
theorem cacheInv_pure {SF : EVMState} {path : UInt256} {sibs : ℕ → UInt256}
    {idx0 cur0 : UInt256} {height : ℕ}
    (σ' : EVMState) (i idx cur : UInt256) (k : ℕ)
    (hg : CacheInv SF path sibs idx0 cur0 height σ' i idx cur (k + 1)) :
    (accOut σ' cur (sibs i.val)).1 = hashOf SF cur (sibs i.val)
      ∧ (accOut σ' (sibs i.val) cur).1 = hashOf SF (sibs i.val) cur := by
  obtain ⟨hsum, hidx, hcur, hframe, hcache, hsibs⟩ := hg
  have hlt : i.val < height := by omega
  obtain ⟨⟨r₁, hSF₁, hσ₁⟩, ⟨r₂, hSF₂, hσ₂⟩⟩ := hcache i.val hlt
  rw [hcur] at *
  exact ⟨accOut_eq_hashOf hframe hSF₁ hσ₁, accOut_eq_hashOf hframe hSF₂ hσ₂⟩

/-- **THE SIBLING READ, DISCHARGED.** -/
theorem cacheInv_sib {SF : EVMState} {path : UInt256} {sibs : ℕ → UInt256}
    {idx0 cur0 : UInt256} {height : ℕ}
    (σ' : EVMState) (i idx cur : UInt256) (k : ℕ)
    (hg : CacheInv SF path sibs idx0 cur0 height σ' i idx cur (k + 1)) :
    σ'.mload ((path + Fin.shiftLeft i 5) + 32) = sibs i.val := by
  obtain ⟨hsum, -, -, -, -, hsibs⟩ := hg
  exact hsibs i (by omega)

/-- **CLOSURE, DISCHARGED.**  The invariant survives one hash step, in whichever orientation
the parity bit selects.  Each conjunct uses the closure lemma written for it:
`accOut_junk_window`, `accOut_lookup_mono`, `accOut_mload_high`. -/
theorem cacheInv_closed {SF : EVMState} {path : UInt256} {sibs : ℕ → UInt256}
    {idx0 cur0 : UInt256} {height : ℕ}
    (hheight : height < 2 ^ 256)
    (hpath : 96 ≤ path.val) (hpb : path.val + 32 * height + 64 ≤ UInt256.size)
    (σ' : EVMState) (i idx cur : UInt256) (k : ℕ)
    (hg : CacheInv SF path sibs idx0 cur0 height σ' i idx cur (k + 1)) :
    CacheInv SF path sibs idx0 cur0 height
      (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
        else accOut σ' (sibs i.val) cur).2
      (i + 1) (Fin.shiftRight idx 1)
      (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
        else accOut σ' (sibs i.val) cur).1 k := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  obtain ⟨hsum, hidx, hcur, hframe, hcache, hsibsr⟩ := hg
  have hlt : i.val < height := by omega
  have h1 : ((1 : UInt256)).val = 1 := by decide
  have hisucc : (i + 1).val = i.val + 1 := by
    rw [Fin.val_add, h1]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hp0, hp1⟩ := cacheInv_pure σ' i idx cur k
    ⟨hsum, hidx, hcur, hframe, hcache, hsibsr⟩
  -- the frame facts hold of BOTH possible post-states, so prove them once per orientation
  have frame_of : ∀ (a b : UInt256),
      (∀ x : UInt256, 64 ≤ x.val → x.val ≤ 94 →
        Finmap.lookup x SF.machine_state.memory
          = Finmap.lookup x (accOut σ' a b).2.machine_state.memory)
      ∧ (∀ l : ℕ, l < height →
        (∃ r : UInt256,
          Finmap.lookup (accInterval SF (accAt (hashOf SF) sibs idx0.val cur0 l) (sibs l))
            SF.keccak_map = some r
          ∧ Finmap.lookup (accInterval SF (accAt (hashOf SF) sibs idx0.val cur0 l) (sibs l))
            (accOut σ' a b).2.keccak_map = some r)
        ∧ (∃ r : UInt256,
          Finmap.lookup (accInterval SF (sibs l) (accAt (hashOf SF) sibs idx0.val cur0 l))
            SF.keccak_map = some r
          ∧ Finmap.lookup (accInterval SF (sibs l) (accAt (hashOf SF) sibs idx0.val cur0 l))
            (accOut σ' a b).2.keccak_map = some r))
      ∧ (∀ j : UInt256, j.val ≤ height →
        (accOut σ' a b).2.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val) := by
    intro a b
    refine ⟨?_, ?_, ?_⟩
    · intro x hx1 hx2
      rw [accOut_junk_window hx1]
      exact hframe x hx1 hx2
    · intro l hl
      obtain ⟨⟨r₁, hSF₁, hσ₁⟩, ⟨r₂, hSF₂, hσ₂⟩⟩ := hcache l hl
      exact ⟨⟨r₁, hSF₁, accOut_lookup_mono hσ₁⟩, ⟨r₂, hSF₂, accOut_lookup_mono hσ₂⟩⟩
    · intro j hj
      have hav : ((path + Fin.shiftLeft j 5) + 32).val = path.val + 32 * j.val + 32 :=
        sib_addr_val (by omega) hj
      rw [accOut_mload_high (by rw [hav]; omega) (by rw [hav]; omega)]
      exact hsibsr j hj
  -- the accumulator advances to the walk's next value
  have hnext : (if Fin.land idx 1 = 0 then accOut σ' cur (sibs i.val)
        else accOut σ' (sibs i.val) cur).1
      = accAt (hashOf SF) sibs idx0.val cur0 (i.val + 1) := by
    have hpar : idx.val % 2 = (idx0.val / 2 ^ i.val) % 2 := by rw [hidx]
    by_cases hb : Fin.land idx 1 = 0
    · rw [if_pos hb, hp0, hcur]
      have hz : (idx0.val / 2 ^ i.val) % 2 = 0 := by
        rw [← hpar]; exact (land_one_eq_zero_iff idx).mp hb
      show _ = if (idx0.val / 2 ^ i.val) % 2 = 1 then _ else _
      rw [if_neg (by omega)]
    · rw [if_neg hb, hp1, hcur]
      have hz : (idx0.val / 2 ^ i.val) % 2 = 1 := by
        rw [← hpar]; exact (land_one_ne_zero_iff idx).mp hb
      show _ = if (idx0.val / 2 ^ i.val) % 2 = 1 then _ else _
      rw [if_pos hz]
  refine ⟨by rw [hisucc]; omega, ?_, by rw [hisucc]; exact hnext, ?_, ?_, ?_⟩
  · rw [shiftRight_one_val, hidx, hisucc, Nat.div_div_eq_div_mul, pow_succ]
  all_goals {
    by_cases hb : Fin.land idx 1 = 0
    · rw [if_pos hb]
      first
        | exact (frame_of cur (sibs i.val)).1
        | exact (frame_of cur (sibs i.val)).2.1
        | exact (frame_of cur (sibs i.val)).2.2
    · rw [if_neg hb]
      first
        | exact (frame_of (sibs i.val) cur).1
        | exact (frame_of (sibs i.val) cur).2.1
        | exact (frame_of (sibs i.val) cur).2.2
  }

/-! ## THE START STATE, AND THE CAPSTONE

The invariant holds at the builder's OWN end state: there the frame condition is reflexivity
and the cache clause is its own hypothesis, so all that is really required is that the state
hashed the walk's pairs and holds the sibling array. -/

/-- **THE INVARIANT AT THE START.**  A state that has hashed every pair the walk uses and holds
the sibling array satisfies `CacheInv` at level `0` with `height` steps to go.

Taking the reference state to be the state itself makes junk-window agreement reflexive — this
is the shape a builder's end state has. -/
theorem cacheInv_start {SF : EVMState} {path : UInt256} {sibs : ℕ → UInt256}
    {idx0 cur0 : UInt256} {height : ℕ}
    (hcache : ∀ l : ℕ, l < height →
      (∃ r : UInt256,
        Finmap.lookup (accInterval SF (accAt (hashOf SF) sibs idx0.val cur0 l) (sibs l))
          SF.keccak_map = some r)
      ∧ (∃ r : UInt256,
        Finmap.lookup (accInterval SF (sibs l) (accAt (hashOf SF) sibs idx0.val cur0 l))
          SF.keccak_map = some r))
    (hsibs : ∀ j : UInt256, j.val ≤ height →
      SF.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val) :
    CacheInv SF path sibs idx0 cur0 height SF 0 idx0 cur0 height := by
  have h0 : ((0 : UInt256)).val = 0 := by decide
  refine ⟨by rw [h0]; omega, ?_, ?_, fun _ _ _ => rfl, ?_, hsibs⟩
  · rw [h0, pow_zero, Nat.div_one]
  · rw [h0]; rfl
  · intro l hl
    obtain ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩ := hcache l hl
    exact ⟨⟨r₁, h₁, h₁⟩, ⟨r₂, h₂, h₂⟩⟩

/-- **THE FOLD CORRESPONDENCE, FULLY INSTANTIATED.**  The contract's `foldRoot` computes exactly
`rootOf (hashOf SF) z0 (leaves.set idx0 cur0) height` — with no abstract hash and no
unsatisfiable hypothesis anywhere in the statement.

What remains are facts about the RUN, all of them finite and checkable:
* `hpath` / `hpb` — the sibling array sits above the keccak scratch and does not wrap;
* the `CacheInv` at the start — the state hashed the walk's pairs and holds the siblings;
* `hsibs` — the sibling stream is the tree's, i.e. M-A's requirement on the path.

The hash is `CachedHash.hashOf SF`, read off the reference state's keccak cache, because Clear's
keccak is freshness-based and no global pure keccak exists. -/
theorem foldRoot_eq_rootOf_cached
    {SF : EVMState} {path : UInt256} {sibs : ℕ → UInt256}
    {idx0 cur0 : UInt256} {height : ℕ} (z0 : UInt256)
    (hheight : height < 2 ^ 256)
    (hpath : 96 ≤ path.val) (hpb : path.val + 32 * height + 64 ≤ UInt256.size)
    {leaves : List UInt256} {σ : EVMState}
    (hg : CacheInv SF path sibs idx0 cur0 height σ 0 idx0 cur0 height)
    (hidx : idx0.val < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels (hashOf SF) z0 (leaves.set idx0.val cur0) l).getD
        (sibIdx (idx0.val / 2 ^ l)) (zeros (hashOf SF) z0 l)) :
    (foldRoot σ path height 0 idx0 cur0).1
      = rootOf (hashOf SF) z0 (leaves.set idx0.val cur0) height :=
  foldRoot_eq_rootOf_of_stepInv (hashOf SF) z0 path sibs
    (CacheInv SF path sibs idx0 cur0 height)
    (fun σ' i idx cur k hgg => cacheInv_sib σ' i idx cur k hgg)
    (fun σ' i idx cur k hgg => cacheInv_pure σ' i idx cur k hgg)
    (fun σ' i idx cur k hgg => cacheInv_closed hheight hpath hpb σ' i idx cur k hgg)
    leaves idx0 cur0 height σ hg hheight hidx hcap hsibs

/-- The same, started from the builder's own end state — the form a real run produces. -/
theorem foldRoot_eq_rootOf_cached_self
    {SF : EVMState} {path : UInt256} {sibs : ℕ → UInt256}
    {idx0 cur0 : UInt256} {height : ℕ} (z0 : UInt256)
    (hheight : height < 2 ^ 256)
    (hpath : 96 ≤ path.val) (hpb : path.val + 32 * height + 64 ≤ UInt256.size)
    {leaves : List UInt256}
    (hcache : ∀ l : ℕ, l < height →
      (∃ r : UInt256,
        Finmap.lookup (accInterval SF (accAt (hashOf SF) sibs idx0.val cur0 l) (sibs l))
          SF.keccak_map = some r)
      ∧ (∃ r : UInt256,
        Finmap.lookup (accInterval SF (sibs l) (accAt (hashOf SF) sibs idx0.val cur0 l))
          SF.keccak_map = some r))
    (hsibsread : ∀ j : UInt256, j.val ≤ height →
      SF.mload ((path + Fin.shiftLeft j 5) + 32) = sibs j.val)
    (hidx : idx0.val < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels (hashOf SF) z0 (leaves.set idx0.val cur0) l).getD
        (sibIdx (idx0.val / 2 ^ l)) (zeros (hashOf SF) z0 l)) :
    (foldRoot SF path height 0 idx0 cur0).1
      = rootOf (hashOf SF) z0 (leaves.set idx0.val cur0) height :=
  foldRoot_eq_rootOf_cached z0 hheight hpath hpb (cacheInv_start hcache hsibsread) hidx hcap hsibs

end Clear.FoldCacheInv
