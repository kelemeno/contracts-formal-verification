import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakFresh
import specs.KeccakSlotSep

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_update_fold_user
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  BUILDER–VERIFIER AGREEMENT, layer 1 — the one-level replay atoms.

  The walk caches each level's pair hash (`accOut_caches_of_clean`); a later
  verifier fold re-computes the same pair on its own evm.  Provided (i) the
  verifier's keccak cache contains the walk's entries (cache transport) and
  (ii) the two evms agree on the scratch junk window `[64, 95)` (the only
  bytes of the hash preimage not overwritten by the pair `mstore`s), the fold
  step is a CACHE HIT returning the walk's value, and it leaves the cache
  untouched — so hits chain.  These are the induction atoms for the agreement
  theorem `foldRoot`-over-walk-siblings = walk root.

  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- **One-level cross-evm agreement.**  If the pair `(a, b)`'s hash is cached
(under the *walk-side* memory `σw`) with value `r`, the cache has been
transported into the verifier evm `σv`, and the two evms agree on the junk
window, then the verifier's pair-hash step returns exactly `r`. -/
theorem accOut_agree
    {σv σw : EVMState} {a b r : UInt256}
    (hjunk : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σv.machine_state.memory
        = Finmap.lookup i σw.machine_state.memory)
    (hcached : Finmap.lookup (accInterval σw a b) σv.keccak_map = some r) :
    accOut σv a b = (r, (σv.mstore 0 a).mstore 32 b) := by
  apply accOut_of_cached
  rw [accInterval_eq hjunk]
  exact hcached

/-- A cache-hit pair-hash step leaves the keccak cache untouched — hits chain. -/
theorem accOut_cached_keccak_map
    {σ : EVMState} {a b r : UInt256}
    (hcached : Finmap.lookup (accInterval σ a b) σ.keccak_map = some r) :
    (accOut σ a b).2.keccak_map = σ.keccak_map := by
  rw [accOut_of_cached hcached]
  rfl

/-- A cache-hit pair-hash step preserves the junk window `[64, 95)`. -/
theorem accOut_cached_junk
    {σ : EVMState} {a b r : UInt256} {i : UInt256}
    (hcached : Finmap.lookup (accInterval σ a b) σ.keccak_map = some r)
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (accOut σ a b).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory :=
  accOut_junk_window hi

/-- A pair-hash step preserves all path-array reads (`≥ 96`). -/
theorem accOut_path_read
    {σ : EVMState} {a b p' : UInt256}
    (hp : 96 ≤ p'.val) (hnw : p'.val + 32 ≤ 2 ^ 256) :
    (accOut σ a b).2.mload p' = σ.mload p' :=
  accOut_mload_high hp hnw

/-- The verifier fold as a tuple walk `(evm, i, idx, cur)` — the prefix-state
form needed for induction-friendly hypotheses. -/
def foldWalk (p : UInt256) : ℕ → EVMState → UInt256 → UInt256 → UInt256
    → EVMState × UInt256 × UInt256 × UInt256
  | 0, σ, i, idx, cur => (σ, i, idx, cur)
  | (j+1), σ, i, idx, cur =>
      foldWalk p j
        (if Fin.land idx 1 = 0
          then accOut σ cur (σ.mload ((p + Fin.shiftLeft i 5) + 32))
          else accOut σ (σ.mload ((p + Fin.shiftLeft i 5) + 32)) cur).2
        (i + 1) (Fin.shiftRight idx 1)
        (if Fin.land idx 1 = 0
          then accOut σ cur (σ.mload ((p + Fin.shiftLeft i 5) + 32))
          else accOut σ (σ.mload ((p + Fin.shiftLeft i 5) + 32)) cur).1

/-- `foldWalk` computes `foldRoot`. -/
lemma foldWalk_foldRoot :
    ∀ (k : ℕ) {σ : EVMState} {p i idx cur : UInt256},
    (foldWalk p k σ i idx cur).2.2.2 = (generated.AtomicFlowManager.AtomicFlowManager.foldRoot σ p k i idx cur).1
      ∧ (foldWalk p k σ i idx cur).1 = (generated.AtomicFlowManager.AtomicFlowManager.foldRoot σ p k i idx cur).2 := by
  intro k
  induction k with
  | zero =>
    intro σ p i idx cur
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro σ p i idx cur
    simp only [foldWalk, generated.AtomicFlowManager.AtomicFlowManager.foldRoot]
    by_cases hpar : Fin.land idx 1 = 0
    · simp only [if_pos hpar]
      exact ih
    · simp only [if_neg hpar]
      exact ih

/-- The sibling value one walk level reads (dispatched). -/
def walkSib (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : UInt256 :=
  if Fin.land t.2.2.1 1 = 0 then
    (if t.2.2.2.1 = t.2.2.1 then (sideRead t.1 (ss + 3) t.2.1).1
     else (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).1)
  else (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).1

/-- The pair-hash output one walk level produces (dispatched — equals the
next walk `cur`). -/
def walkHash (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : UInt256 × EVMState :=
  if Fin.land t.2.2.1 1 = 0 then
    (if t.2.2.2.1 = t.2.2.1 then
      accOut (sideRead t.1 (ss + 3) t.2.1).2 t.2.2.2.2 (sideRead t.1 (ss + 3) t.2.1).1
     else accOut (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).2 t.2.2.2.2
        (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).1)
  else accOut (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).2
      (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).1 t.2.2.2.2

private lemma arrOut_lookup_mono
    {σ : EVMState} {a : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (arrOut σ a).2.keccak_map = some w := by
  apply keccakOut_lookup_mono
  rwa [keccak_map_mstore]

/-- `sstore` does not touch the keccak cache. -/
private lemma keccak_map_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).keccak_map = σ.keccak_map := by
  unfold EVMState.sstore
  cases h : σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- One walk step only grows the keccak cache. -/
lemma updateStep_lookup_mono
    {σ : EVMState} {ss base i idx maxN cur : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I ((updateStep σ ss base i idx maxN cur).2).keccak_map = some w := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      rw [keccak_map_sstore]
      exact arrOut_lookup_mono (arrOut_lookup_mono (accOut_lookup_mono
        (arrOut_lookup_mono hI)))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      rw [keccak_map_sstore]
      exact arrOut_lookup_mono (arrOut_lookup_mono (accOut_lookup_mono
        (arrOut_lookup_mono (arrOut_lookup_mono hI))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    rw [keccak_map_sstore]
    exact arrOut_lookup_mono (arrOut_lookup_mono (accOut_lookup_mono
      (arrOut_lookup_mono (arrOut_lookup_mono hI))))

/-- The whole walk only grows the keccak cache. -/
lemma updateWalk_lookup_mono :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256}
      {I : List UInt256} {w : UInt256},
    Finmap.lookup I σ.keccak_map = some w →
    Finmap.lookup I ((updateWalk ss base k σ i idx maxN cur).1).keccak_map = some w := by
  intro k
  induction k with
  | zero =>
    intro σ ss base i idx maxN cur I w hI
    exact hI
  | succ k ih =>
    intro σ ss base i idx maxN cur I w hI
    simp only [updateWalk]
    exact ih (updateStep_lookup_mono hI)

/-- The walk's pre-hash evm at one level (post sibling read, dispatched). -/
def walkPreHash (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : EVMState :=
  if Fin.land t.2.2.1 1 = 0 then
    (if t.2.2.2.1 = t.2.2.1 then (sideRead t.1 (ss + 3) t.2.1).2
     else (sibRead t.1 base t.2.1 (t.2.2.1 + 1)).2)
  else (sibRead t.1 base t.2.1 (t.2.2.1 - 1)).2

/-- The pair hashed at one walk level, in fold orientation `(a, b)`. -/
def walkPair (ss base : UInt256)
    (t : EVMState × UInt256 × UInt256 × UInt256 × UInt256) : UInt256 × UInt256 :=
  if Fin.land t.2.2.1 1 = 0 then (t.2.2.2.2, walkSib ss base t)
  else (walkSib ss base t, t.2.2.2.2)

/-- The scratch `mstore`s preserve the junk window `[64, 95)`. -/
private lemma mstore_junk {σ : EVMState} {a v : UInt256} {i : UInt256}
    (ha : a.val + 32 ≤ 64) (hi : 64 ≤ i.val) :
    Finmap.lookup i (σ.mstore a v).machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  apply lookup_updateMemory_outside_val
  · omega
  · right
    omega

/-- **THE AGREEMENT INDUCTION.**  If, level by level, the verifier fold reads
the walk's sibling, the walk's pair-hash entry is in the verifier's cache
(interval over the walk's pre-hash memory), and the two memories agree on the
junk window, then the fold reproduces the walk's node chain — and the fold
leaves its cache and junk window untouched. -/
theorem fold_walk_agree :
    ∀ (k : ℕ) {σv σw : EVMState} {p iv : UInt256}
      {ss base iw idx maxN cur : UInt256},
    (∀ j, j < k →
      (foldWalk p j σv iv idx cur).1.mload
          ((p + Fin.shiftLeft (foldWalk p j σv iv idx cur).2.1 5) + 32)
        = walkSib ss base (updateWalk ss base j σw iw idx maxN cur)) →
    (∀ j, j < k →
      Finmap.lookup
        (accInterval (walkPreHash ss base (updateWalk ss base j σw iw idx maxN cur))
          (walkPair ss base (updateWalk ss base j σw iw idx maxN cur)).1
          (walkPair ss base (updateWalk ss base j σw iw idx maxN cur)).2)
        σv.keccak_map
      = some (walkHash ss base (updateWalk ss base j σw iw idx maxN cur)).1) →
    (∀ j, j < k → ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σv.machine_state.memory
        = Finmap.lookup i
            (walkPreHash ss base (updateWalk ss base j σw iw idx maxN cur)).machine_state.memory) →
    (foldWalk p k σv iv idx cur).2.2.2
        = (updateWalk ss base k σw iw idx maxN cur).2.2.2.2
      ∧ (foldWalk p k σv iv idx cur).1.keccak_map = σv.keccak_map
      ∧ (∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
          Finmap.lookup i (foldWalk p k σv iv idx cur).1.machine_state.memory
            = Finmap.lookup i σv.machine_state.memory)
      ∧ (foldWalk p k σv iv idx cur).1.hash_collision = σv.hash_collision := by
  intro k
  induction k with
  | zero =>
    intro σv σw p iv ss base iw idx maxN cur _ _ _
    exact ⟨rfl, rfl, fun _ _ _ => rfl, rfl⟩
  | succ k ih =>
    intro σv σw p iv ss base iw idx maxN cur hsib hcached hjunk
    have hsib0 := hsib 0 (by omega)
    have hcached0 := hcached 0 (by omega)
    have hjunk0 := hjunk 0 (by omega)
    simp only [foldWalk, updateWalk] at hsib0 hcached0 hjunk0 ⊢
    -- the level-0 fold hash is a cache hit returning the walk's node
    have hagree :
        (if Fin.land idx 1 = 0
          then accOut σv cur (σv.mload ((p + Fin.shiftLeft iv 5) + 32))
          else accOut σv (σv.mload ((p + Fin.shiftLeft iv 5) + 32)) cur)
        = ((walkHash ss base (σw, iw, idx, maxN, cur)).1,
           (if Fin.land idx 1 = 0
            then (σv.mstore 0 cur).mstore 32 (σv.mload ((p + Fin.shiftLeft iv 5) + 32))
            else (σv.mstore 0 (σv.mload ((p + Fin.shiftLeft iv 5) + 32))).mstore 32 cur)) := by
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar, if_pos hpar]
        rw [hsib0]
        have := accOut_agree (σw := walkPreHash ss base (σw, iw, idx, maxN, cur))
          (a := cur) (b := walkSib ss base (σw, iw, idx, maxN, cur))
          (r := (walkHash ss base (σw, iw, idx, maxN, cur)).1)
          hjunk0
          (by
            have h := hcached0
            unfold walkPair at h
            rw [if_pos hpar] at h
            exact h)
        rw [this]
      · rw [if_neg hpar, if_neg hpar]
        rw [hsib0]
        have := accOut_agree (σw := walkPreHash ss base (σw, iw, idx, maxN, cur))
          (a := walkSib ss base (σw, iw, idx, maxN, cur)) (b := cur)
          (r := (walkHash ss base (σw, iw, idx, maxN, cur)).1)
          hjunk0
          (by
            have h := hcached0
            unfold walkPair at h
            rw [if_neg hpar] at h
            exact h)
        rw [this]
    -- the walk's next node equals its level hash
    have hwstep : (updateStep σw ss base iw idx maxN cur).1
        = (walkHash ss base (σw, iw, idx, maxN, cur)).1 := by
      unfold updateStep walkHash
      by_cases hpar : Fin.land idx 1 = 0
      · by_cases hedge : maxN = idx
        · rw [if_pos hpar, if_pos hedge, if_pos hpar, if_pos hedge]
          rfl
        · rw [if_pos hpar, if_neg hedge, if_pos hpar, if_neg hedge]
          rfl
      · rw [if_neg hpar, if_neg hpar]
        rfl
    rw [hagree]
    -- the fold's next base state: cache and junk of σv preserved (mstores only)
    set σv' := (if Fin.land idx 1 = 0
        then (σv.mstore 0 cur).mstore 32 (σv.mload ((p + Fin.shiftLeft iv 5) + 32))
        else (σv.mstore 0 (σv.mload ((p + Fin.shiftLeft iv 5) + 32))).mstore 32 cur)
      with hσv'
    have hcachev' : σv'.keccak_map = σv.keccak_map := by
      rw [hσv']
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar]
        rfl
      · rw [if_neg hpar]
        rfl
    have hjunkv' : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i σv'.machine_state.memory
          = Finmap.lookup i σv.machine_state.memory := by
      intro i hi hi'
      rw [hσv']
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar]
        rw [mstore_junk (by decide) hi, mstore_junk (by decide) hi]
      · rw [if_neg hpar]
        rw [mstore_junk (by decide) hi, mstore_junk (by decide) hi]
    have hflagv' : σv'.hash_collision = σv.hash_collision := by
      rw [hσv']
      by_cases hpar : Fin.land idx 1 = 0
      · rw [if_pos hpar]
        rfl
      · rw [if_neg hpar]
        rfl
    -- apply the IH at the shifted states
    have := ih (σv := σv') (σw := (updateStep σw ss base iw idx maxN cur).2)
      (p := p) (iv := iv + 1) (ss := ss) (base := base) (iw := iw + 1)
      (idx := Fin.shiftRight idx 1) (maxN := Fin.shiftRight maxN 1)
      (cur := (walkHash ss base (σw, iw, idx, maxN, cur)).1)
      (by
        intro j hj
        have h := hsib (j+1) (by omega)
        simp only [foldWalk, updateWalk] at h
        rw [hagree, hwstep] at h
        exact h)
      (by
        intro j hj
        have h := hcached (j+1) (by omega)
        simp only [updateWalk] at h
        rw [hwstep] at h
        rw [hcachev']
        exact h)
      (by
        intro j hj i hi hi'
        have h := hjunk (j+1) (by omega)
        simp only [updateWalk] at h
        rw [hwstep] at h
        rw [hjunkv' i hi hi']
        exact h i hi hi')
    obtain ⟨hval, hcache, hjunkf, hflag⟩ := this
    rw [hwstep]
    refine ⟨hval, ?_, ?_, ?_⟩
    · rw [hcache, hcachev']
    · intro i hi hi'
      rw [hjunkf i hi hi', hjunkv' i hi hi']
    · rw [hflag, hflagv']

/-! ### The pool invariants cross the walk

Companions to `updateStep_lookup_mono` / `updateWalk_lookup_mono`, for the three properties
the derived (axiom-free) separation route consumes.  Same shape: case on the step's three
branches, then induct on the level count.

These are what a `_of_config` twin of anything downstream of a walk needs -- without them
the properties stop at the walk's entry state and the derived route cannot be stated past
it. -/

lemma separated_updateStep {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (h : Clear.KeccakSlotSep.Separated σ) :
    Clear.KeccakSlotSep.Separated ((updateStep σ ss base i idx maxN cur).2) := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      exact Clear.StorageFrame.separated_sstore (separated_arrOut (separated_arrOut
        (separated_accOut (separated_arrOut h))))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      exact Clear.StorageFrame.separated_sstore (separated_arrOut (separated_arrOut
        (separated_accOut (separated_arrOut (separated_arrOut h)))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    exact Clear.StorageFrame.separated_sstore (separated_arrOut (separated_arrOut
      (separated_accOut (separated_arrOut (separated_arrOut h)))))

lemma separated_updateWalk :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    Clear.KeccakSlotSep.Separated σ →
    Clear.KeccakSlotSep.Separated ((updateWalk ss base k σ i idx maxN cur).1) := by
  intro k
  induction k with
  | zero => intro σ ss base i idx maxN cur h; exact h
  | succ k ih =>
    intro σ ss base i idx maxN cur h
    simp only [updateWalk]
    exact ih (separated_updateStep h)

/-- `CacheInUsed` first: `CacheInj`'s step lemma consumes it, so the two travel together. -/
lemma cacheInUsed_updateStep {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (h : Clear.KeccakFresh.CacheInUsed σ) :
    Clear.KeccakFresh.CacheInUsed ((updateStep σ ss base i idx maxN cur).2) := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      exact Clear.StorageFrame.cacheInUsed_sstore (cacheInUsed_arrOut (cacheInUsed_arrOut
        (Clear.KeccakFresh.cacheInUsed_accOut (cacheInUsed_arrOut h))))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      exact Clear.StorageFrame.cacheInUsed_sstore (cacheInUsed_arrOut (cacheInUsed_arrOut
        (Clear.KeccakFresh.cacheInUsed_accOut (cacheInUsed_arrOut (cacheInUsed_arrOut h)))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    exact Clear.StorageFrame.cacheInUsed_sstore (cacheInUsed_arrOut (cacheInUsed_arrOut
      (Clear.KeccakFresh.cacheInUsed_accOut (cacheInUsed_arrOut (cacheInUsed_arrOut h)))))

lemma cacheInj_updateStep {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (hu : Clear.KeccakFresh.CacheInUsed σ) (h : Clear.KeccakFresh.CacheInj σ) :
    Clear.KeccakFresh.CacheInj ((updateStep σ ss base i idx maxN cur).2) := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      exact Clear.StorageFrame.cacheInj_sstore (cacheInj_arrOut
        (cacheInUsed_arrOut (Clear.KeccakFresh.cacheInUsed_accOut (cacheInUsed_arrOut hu)))
        (cacheInj_arrOut (Clear.KeccakFresh.cacheInUsed_accOut (cacheInUsed_arrOut hu))
          (Clear.KeccakFresh.cacheInj_accOut (cacheInUsed_arrOut hu)
            (cacheInj_arrOut hu h))))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      exact Clear.StorageFrame.cacheInj_sstore (cacheInj_arrOut
        (cacheInUsed_arrOut (Clear.KeccakFresh.cacheInUsed_accOut
          (cacheInUsed_arrOut (cacheInUsed_arrOut hu))))
        (cacheInj_arrOut (Clear.KeccakFresh.cacheInUsed_accOut
            (cacheInUsed_arrOut (cacheInUsed_arrOut hu)))
          (Clear.KeccakFresh.cacheInj_accOut
            (cacheInUsed_arrOut (cacheInUsed_arrOut hu))
            (cacheInj_arrOut (cacheInUsed_arrOut hu) (cacheInj_arrOut hu h)))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    exact Clear.StorageFrame.cacheInj_sstore (cacheInj_arrOut
      (cacheInUsed_arrOut (Clear.KeccakFresh.cacheInUsed_accOut
        (cacheInUsed_arrOut (cacheInUsed_arrOut hu))))
      (cacheInj_arrOut (Clear.KeccakFresh.cacheInUsed_accOut
          (cacheInUsed_arrOut (cacheInUsed_arrOut hu)))
        (Clear.KeccakFresh.cacheInj_accOut
          (cacheInUsed_arrOut (cacheInUsed_arrOut hu))
          (cacheInj_arrOut (cacheInUsed_arrOut hu) (cacheInj_arrOut hu h)))))

lemma cacheInUsed_updateWalk :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    Clear.KeccakFresh.CacheInUsed σ →
    Clear.KeccakFresh.CacheInUsed ((updateWalk ss base k σ i idx maxN cur).1) := by
  intro k
  induction k with
  | zero => intro σ ss base i idx maxN cur h; exact h
  | succ k ih =>
    intro σ ss base i idx maxN cur h
    simp only [updateWalk]
    exact ih (cacheInUsed_updateStep h)

lemma cacheInj_updateWalk :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    Clear.KeccakFresh.CacheInUsed σ → Clear.KeccakFresh.CacheInj σ →
    Clear.KeccakFresh.CacheInj ((updateWalk ss base k σ i idx maxN cur).1) := by
  intro k
  induction k with
  | zero => intro σ ss base i idx maxN cur _ h; exact h
  | succ k ih =>
    intro σ ss base i idx maxN cur hu h
    simp only [updateWalk]
    exact ih (cacheInUsed_updateStep hu) (cacheInj_updateStep hu h)

/-! ## The low-slot window config crosses the update walk

The third property pair, transported the same way as `Separated` / `CacheInj` above.
`keccak256_add_ne_lowSlot_of_config` and `keccak256_ne_lowSlot_of_config` consume these,
so the walk-level low-slot frames cannot leave the axiomatic route without them. -/

lemma rangeInWindow_updateStep {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) :
    Clear.KeccakLowSlot.RangeInWindow ((updateStep σ ss base i idx maxN cur).2) := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      exact Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_arrOut
        (rangeInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut hR))))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      exact Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_arrOut
        (rangeInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut
          (rangeInWindow_arrOut hR)))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    exact Clear.StorageFrame.rangeInWindow_sstore (rangeInWindow_arrOut
      (rangeInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut
        (rangeInWindow_arrOut hR)))))

lemma cachedInWindow_updateStep {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ)
    (hC : Clear.KeccakLowSlot.CachedInWindow σ) :
    Clear.KeccakLowSlot.CachedInWindow ((updateStep σ ss base i idx maxN cur).2) := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore sideRead
      exact Clear.StorageFrame.cachedInWindow_sstore (cachedInWindow_arrOut
        (rangeInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut hR)))
        (cachedInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut hR))
          (cachedInWindow_accOut (rangeInWindow_arrOut hR)
            (cachedInWindow_arrOut hR hC))))
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore sibRead
      exact Clear.StorageFrame.cachedInWindow_sstore (cachedInWindow_arrOut
        (rangeInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut
          (rangeInWindow_arrOut hR))))
        (cachedInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut
            (rangeInWindow_arrOut hR)))
          (cachedInWindow_accOut (rangeInWindow_arrOut (rangeInWindow_arrOut hR))
            (cachedInWindow_arrOut (rangeInWindow_arrOut hR)
              (cachedInWindow_arrOut hR hC)))))
  · rw [if_neg hpar]
    unfold stepOdd nodeStore sibRead
    exact Clear.StorageFrame.cachedInWindow_sstore (cachedInWindow_arrOut
      (rangeInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut
        (rangeInWindow_arrOut hR))))
      (cachedInWindow_arrOut (rangeInWindow_accOut (rangeInWindow_arrOut
          (rangeInWindow_arrOut hR)))
        (cachedInWindow_accOut (rangeInWindow_arrOut (rangeInWindow_arrOut hR))
          (cachedInWindow_arrOut (rangeInWindow_arrOut hR)
            (cachedInWindow_arrOut hR hC)))))

lemma rangeInWindow_updateWalk :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    Clear.KeccakLowSlot.RangeInWindow σ →
    Clear.KeccakLowSlot.RangeInWindow ((updateWalk ss base k σ i idx maxN cur).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ _ _ _ h; exact h
  | succ k ih =>
    intro σ ss base i idx maxN cur h
    simp only [updateWalk]
    exact ih (rangeInWindow_updateStep h)

lemma cachedInWindow_updateWalk :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    Clear.KeccakLowSlot.RangeInWindow σ → Clear.KeccakLowSlot.CachedInWindow σ →
    Clear.KeccakLowSlot.CachedInWindow ((updateWalk ss base k σ i idx maxN cur).1) := by
  intro k
  induction k with
  | zero => intro σ _ _ _ _ _ _ _ h; exact h
  | succ k ih =>
    intro σ ss base i idx maxN cur hR hC
    simp only [updateWalk]
    exact ih (rangeInWindow_updateStep hR) (cachedInWindow_updateStep hR hC)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
