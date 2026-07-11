import Clear.ReasoningPrinciple

import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_agreement_user
import specs.AtomicFlowManager.AtomicFlowManager.merkle_binding_user

/-
  BUILDER–VERIFIER AGREEMENT, layer 2 — the concrete replay corollary.

  `fold_walk_agree` (layer 1) takes three per-level hypotheses.  Here we
  discharge them for the canonical replay scenario:

  * **The walk caches its own hashes.**  A collision-free builder walk
    performed each level's pair keccak itself, so the entry
    `accInterval (walkPreHash j) pair ↦ walkHash j` is in the walk's FINAL
    keccak map (`walk_caches`) — created at step `j` (`updateStep_caches`,
    from `accOut_caches_of_clean`) and preserved by the remaining steps
    (`updateWalk_lookup_mono`).

  * **The walk never touches the junk window.**  Every memory write along the
    walk is an `mstore` at 0 or 32 (`arrOut`/`accOut` scratch); `sstore` does
    not touch memory.  So `[64, 95)` is invariant along the walk
    (`updateWalk_junk`, `walkPreHash_junk`).

  * **The fold's path reads are reads of its initial memory.**  The fold only
    writes scratch `[0, 64)`, so reads at `≥ 96` see the verifier's starting
    memory (`foldWalk_mload_high`), and the fold's level counter is `iv + j`
    (`foldWalk_index`).

  The corollary `fold_replays_walk`: a verifier evm whose keccak cache
  contains the builder's final cache, whose junk window agrees with the
  builder's initial one, and whose path array holds the siblings the builder
  actually read, folds the SAME leaf to exactly the root the builder stored.
  Composed with `foldRoot_binding` (#27) this closes the loop: the stored
  root verifies the written leaf, and ONLY the written leaf, at its position.

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

/-! ### `sstore` atoms: storage writes touch neither memory, cache, nor flag -/

private lemma machine_state_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).machine_state = σ.machine_state := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

private lemma hash_collision_sstore' (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).hash_collision = σ.hash_collision := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

private lemma keccak_map_sstore' (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).keccak_map = σ.keccak_map := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-! ### `arrOut` atoms: junk window, clean-backward, cache monotonicity -/

private lemma mstore_junk' {σ : EVMState} {a v : UInt256} {i : UInt256}
    (ha : a.val + 32 ≤ 64) (hi : 64 ≤ i.val) :
    Finmap.lookup i (σ.mstore a v).machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  apply lookup_updateMemory_outside_val
  · omega
  · right
    omega

private lemma arrOut_junk {σ : EVMState} {a : UInt256} {i : UInt256}
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (arrOut σ a).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  unfold arrOut
  rw [keccakOut_machine_state]
  exact mstore_junk' (by rw [(by decide : ((0 : UInt256)).val = 0)]; omega) hi

private lemma arrOut_clean_backward' {σ : EVMState} {a : UInt256}
    (h : (arrOut σ a).2.hash_collision = false) :
    σ.hash_collision = false := by
  unfold arrOut at h
  have := keccakOut_clean_backward h
  rwa [hash_collision_mstore] at this

private lemma arrOut_lookup_mono'
    {σ : EVMState} {a : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (arrOut σ a).2.keccak_map = some w := by
  unfold arrOut
  apply keccakOut_lookup_mono
  rwa [keccak_map_mstore]

/-! ### Sibling-read composites -/

private lemma sideRead_junk {σ : EVMState} {slot lvl : UInt256} {i : UInt256}
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (sideRead σ slot lvl).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  unfold sideRead
  rw [arrOut_junk hi]

private lemma sibRead_junk {σ : EVMState} {base lvl j : UInt256} {i : UInt256}
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (sibRead σ base lvl j).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  unfold sibRead
  rw [arrOut_junk hi, arrOut_junk hi]

private lemma sideRead_clean_backward {σ : EVMState} {slot lvl : UInt256}
    (h : (sideRead σ slot lvl).2.hash_collision = false) :
    σ.hash_collision = false := by
  unfold sideRead at h
  exact arrOut_clean_backward' h

private lemma sibRead_clean_backward {σ : EVMState} {base lvl j : UInt256}
    (h : (sibRead σ base lvl j).2.hash_collision = false) :
    σ.hash_collision = false := by
  unfold sibRead at h
  exact arrOut_clean_backward' (arrOut_clean_backward' h)

/-! ### Junk-window invariance of one walk step and of the whole walk -/

lemma updateStep_junk
    {σ : EVMState} {ss base i idx maxN cur : UInt256} {a : UInt256}
    (ha : 64 ≤ a.val) :
    Finmap.lookup a ((updateStep σ ss base i idx maxN cur).2).machine_state.memory
      = Finmap.lookup a σ.machine_state.memory := by
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      unfold stepEdge nodeStore
      rw [machine_state_sstore, arrOut_junk ha, arrOut_junk ha,
          accOut_junk_window ha, sideRead_junk ha]
    · rw [if_pos hpar, if_neg hedge]
      unfold stepEven nodeStore
      rw [machine_state_sstore, arrOut_junk ha, arrOut_junk ha,
          accOut_junk_window ha, sibRead_junk ha]
  · rw [if_neg hpar]
    unfold stepOdd nodeStore
    rw [machine_state_sstore, arrOut_junk ha, arrOut_junk ha,
        accOut_junk_window ha, sibRead_junk ha]

lemma updateWalk_junk :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256} {a : UInt256},
    64 ≤ a.val →
    Finmap.lookup a ((updateWalk ss base k σ i idx maxN cur).1).machine_state.memory
      = Finmap.lookup a σ.machine_state.memory := by
  intro k
  induction k with
  | zero =>
    intro σ ss base i idx maxN cur a _
    rfl
  | succ k ih =>
    intro σ ss base i idx maxN cur a ha
    simp only [updateWalk]
    rw [ih ha, updateStep_junk ha]

/-- The pre-hash state at one walk level agrees with the level's input state
on the junk window (the sibling read only writes scratch `[0, 32)`). -/
lemma walkPreHash_junk
    {ss base : UInt256} {t : EVMState × UInt256 × UInt256 × UInt256 × UInt256}
    {a : UInt256} (ha : 64 ≤ a.val) :
    Finmap.lookup a (walkPreHash ss base t).machine_state.memory
      = Finmap.lookup a t.1.machine_state.memory := by
  unfold walkPreHash
  by_cases hpar : Fin.land t.2.2.1 1 = 0
  · rw [if_pos hpar]
    by_cases hedge : t.2.2.2.1 = t.2.2.1
    · rw [if_pos hedge]
      exact sideRead_junk ha
    · rw [if_neg hedge]
      exact sibRead_junk ha
  · rw [if_neg hpar]
    exact sibRead_junk ha

/-! ### Clean-backward along the walk -/

lemma updateStep_clean_backward
    {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (h : ((updateStep σ ss base i idx maxN cur).2).hash_collision = false) :
    σ.hash_collision = false := by
  unfold updateStep at h
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge] at h
      unfold stepEdge nodeStore at h
      rw [hash_collision_sstore'] at h
      exact sideRead_clean_backward (accOut_clean_backward
        (arrOut_clean_backward' (arrOut_clean_backward' h)))
    · rw [if_pos hpar, if_neg hedge] at h
      unfold stepEven nodeStore at h
      rw [hash_collision_sstore'] at h
      exact sibRead_clean_backward (accOut_clean_backward
        (arrOut_clean_backward' (arrOut_clean_backward' h)))
  · rw [if_neg hpar] at h
    unfold stepOdd nodeStore at h
    rw [hash_collision_sstore'] at h
    exact sibRead_clean_backward (accOut_clean_backward
      (arrOut_clean_backward' (arrOut_clean_backward' h)))

lemma updateWalk_clean_backward :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    ((updateWalk ss base k σ i idx maxN cur).1).hash_collision = false →
    σ.hash_collision = false := by
  intro k
  induction k with
  | zero =>
    intro σ ss base i idx maxN cur h
    exact h
  | succ k ih =>
    intro σ ss base i idx maxN cur h
    simp only [updateWalk] at h
    exact updateStep_clean_backward (ih h)

/-! ### The walk caches its own level hashes -/

private lemma stepOdd_caches
    {σ : EVMState} {base i idx cur : UInt256}
    (h : (stepOdd σ base i idx cur).2.hash_collision = false) :
    Finmap.lookup
        (accInterval (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur)
        (stepOdd σ base i idx cur).2.keccak_map
      = some (stepOdd σ base i idx cur).1 := by
  have hA : (accOut (sibRead σ base i (idx - 1)).2
      (sibRead σ base i (idx - 1)).1 cur).2.hash_collision = false := by
    unfold stepOdd nodeStore at h
    rw [hash_collision_sstore'] at h
    exact arrOut_clean_backward' (arrOut_clean_backward' h)
  have hc := accOut_caches_of_clean hA
  unfold stepOdd nodeStore
  rw [keccak_map_sstore']
  exact arrOut_lookup_mono' (arrOut_lookup_mono' hc)

private lemma stepEven_caches
    {σ : EVMState} {base i idx cur : UInt256}
    (h : (stepEven σ base i idx cur).2.hash_collision = false) :
    Finmap.lookup
        (accInterval (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1)
        (stepEven σ base i idx cur).2.keccak_map
      = some (stepEven σ base i idx cur).1 := by
  have hA : (accOut (sibRead σ base i (idx + 1)).2
      cur (sibRead σ base i (idx + 1)).1).2.hash_collision = false := by
    unfold stepEven nodeStore at h
    rw [hash_collision_sstore'] at h
    exact arrOut_clean_backward' (arrOut_clean_backward' h)
  have hc := accOut_caches_of_clean hA
  unfold stepEven nodeStore
  rw [keccak_map_sstore']
  exact arrOut_lookup_mono' (arrOut_lookup_mono' hc)

private lemma stepEdge_caches
    {σ : EVMState} {ss base i idx cur : UInt256}
    (h : (stepEdge σ ss base i idx cur).2.hash_collision = false) :
    Finmap.lookup
        (accInterval (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1)
        (stepEdge σ ss base i idx cur).2.keccak_map
      = some (stepEdge σ ss base i idx cur).1 := by
  have hA : (accOut (sideRead σ (ss + 3) i).2
      cur (sideRead σ (ss + 3) i).1).2.hash_collision = false := by
    unfold stepEdge nodeStore at h
    rw [hash_collision_sstore'] at h
    exact arrOut_clean_backward' (arrOut_clean_backward' h)
  have hc := accOut_caches_of_clean hA
  unfold stepEdge nodeStore
  rw [keccak_map_sstore']
  exact arrOut_lookup_mono' (arrOut_lookup_mono' hc)

/-- One collision-free walk step caches its level's pair hash: after the step,
`accInterval (walkPreHash t) (walkPair t) ↦ (walkHash t).1` is in the cache. -/
lemma updateStep_caches
    {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (h : ((updateStep σ ss base i idx maxN cur).2).hash_collision = false) :
    Finmap.lookup
        (accInterval (walkPreHash ss base (σ, i, idx, maxN, cur))
          (walkPair ss base (σ, i, idx, maxN, cur)).1
          (walkPair ss base (σ, i, idx, maxN, cur)).2)
        ((updateStep σ ss base i idx maxN cur).2).keccak_map
      = some (walkHash ss base (σ, i, idx, maxN, cur)).1 := by
  unfold updateStep at h ⊢
  unfold walkPreHash walkPair walkSib walkHash
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge] at h
      rw [if_pos hpar, if_pos hedge, if_pos hpar, if_pos hpar, if_pos hedge,
          if_pos hpar, if_pos hedge, if_pos hpar, if_pos hedge]
      exact stepEdge_caches h
    · rw [if_pos hpar, if_neg hedge] at h
      rw [if_pos hpar, if_neg hedge, if_pos hpar, if_pos hpar, if_neg hedge,
          if_pos hpar, if_neg hedge, if_pos hpar, if_neg hedge]
      exact stepEven_caches h
  · rw [if_neg hpar] at h
    rw [if_neg hpar, if_neg hpar, if_neg hpar, if_neg hpar, if_neg hpar]
    exact stepOdd_caches h

/-- **The walk caches all its level hashes.**  If the walk to depth `k` is
collision-free, then for every level `j < k`, the pair-hash entry the walk
computed at level `j` is present in the walk's FINAL keccak map. -/
theorem walk_caches :
    ∀ (k : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256},
    ((updateWalk ss base k σ i idx maxN cur).1).hash_collision = false →
    ∀ j, j < k →
    Finmap.lookup
        (accInterval (walkPreHash ss base (updateWalk ss base j σ i idx maxN cur))
          (walkPair ss base (updateWalk ss base j σ i idx maxN cur)).1
          (walkPair ss base (updateWalk ss base j σ i idx maxN cur)).2)
        ((updateWalk ss base k σ i idx maxN cur).1).keccak_map
      = some (walkHash ss base (updateWalk ss base j σ i idx maxN cur)).1 := by
  intro k
  induction k with
  | zero =>
    intro σ ss base i idx maxN cur _ j hj
    omega
  | succ k ih =>
    intro σ ss base i idx maxN cur hclean j hj
    cases j with
    | zero =>
      simp only [updateWalk] at hclean ⊢
      exact updateWalk_lookup_mono k
        (updateStep_caches (updateWalk_clean_backward k hclean))
    | succ j' =>
      simp only [updateWalk] at hclean ⊢
      exact ih hclean j' (Nat.lt_of_succ_lt_succ hj)

/-! ### The fold's path reads and level counter reduce to its initial state -/

/-- The fold's level counter after `j` levels is `iv + j`. -/
lemma foldWalk_index :
    ∀ (j : ℕ) {σ : EVMState} {p i idx cur : UInt256},
    (foldWalk p j σ i idx cur).2.1 = i + (j : UInt256) := by
  intro j
  induction j with
  | zero =>
    intro σ p i idx cur
    simp [foldWalk]
  | succ j ih =>
    intro σ p i idx cur
    simp only [foldWalk]
    rw [ih, Nat.cast_add, Nat.cast_one]
    ring

/-- The fold only writes scratch `[0, 64)`: reads at `≥ 96` (the path array)
see the verifier's initial memory at every level. -/
lemma foldWalk_mload_high :
    ∀ (j : ℕ) {σ : EVMState} {p i idx cur a : UInt256},
    96 ≤ a.val → a.val + 32 ≤ 2 ^ 256 →
    (foldWalk p j σ i idx cur).1.mload a = σ.mload a := by
  intro j
  induction j with
  | zero =>
    intro σ p i idx cur a _ _
    rfl
  | succ j ih =>
    intro σ p i idx cur a h1 h2
    simp only [foldWalk]
    by_cases hpar : Fin.land idx 1 = 0
    · rw [if_pos hpar, ih h1 h2]
      exact accOut_path_read h1 h2
    · rw [if_neg hpar, ih h1 h2]
      exact accOut_path_read h1 h2

/-! ### THE REPLAY COROLLARY -/

/-- **The verifier fold replays the builder walk.**  Let the builder walk run
`k` collision-free levels from `σw` (leaf `cur` at position `idx`), storing
final root `(updateWalk …).2.2.2.2`.  Let `σv` be any verifier evm such that

* its keccak cache contains the walk's final cache (`hmap` — cache transport;
  in particular `σv` = the post-walk evm itself works),
* its junk window `[64, 95)` agrees with the walk's INITIAL memory (`hjunkv`),
* its path array (at `p`, counter starting at `iv`, in-bounds by
  `hlo`/`hhi`) holds exactly the siblings the walk read (`hsibs`).

Then the verifier fold of the SAME leaf `cur` at the SAME position `idx`
computes exactly the root the builder stored. -/
theorem fold_replays_walk
    (k : ℕ) {σv σw : EVMState} {p ss base iv iw idx maxN cur : UInt256}
    (hclean : ((updateWalk ss base k σw iw idx maxN cur).1).hash_collision = false)
    (hmap : ∀ (I : List UInt256) (w : UInt256),
        Finmap.lookup I ((updateWalk ss base k σw iw idx maxN cur).1).keccak_map = some w →
        Finmap.lookup I σv.keccak_map = some w)
    (hjunkv : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i σv.machine_state.memory
          = Finmap.lookup i σw.machine_state.memory)
    (hlo : ∀ j : ℕ, j < k →
        96 ≤ ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32).val)
    (hhi : ∀ j : ℕ, j < k →
        ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32).val + 32 ≤ 2 ^ 256)
    (hsibs : ∀ j : ℕ, j < k →
        σv.mload ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32)
          = walkSib ss base (updateWalk ss base j σw iw idx maxN cur)) :
    (generated.AtomicFlowManager.AtomicFlowManager.foldRoot σv p k iv idx cur).1
      = (updateWalk ss base k σw iw idx maxN cur).2.2.2.2 := by
  rw [← (foldWalk_foldRoot k).1]
  refine (fold_walk_agree k ?_ ?_ ?_).1
  · intro j hj
    rw [foldWalk_index j, foldWalk_mload_high j (hlo j hj) (hhi j hj)]
    exact hsibs j hj
  · intro j hj
    exact hmap _ _ (walk_caches k hclean j hj)
  · intro j hj i hi1 hi2
    rw [hjunkv i hi1 hi2, walkPreHash_junk hi1, updateWalk_junk j hi1]

/-- **The replay fold stays collision-free.**  Under the replay hypotheses,
every fold level is a cache hit, so the fold's post-state carries the
verifier's own collision flag: a clean verifier evm yields a clean fold. -/
theorem fold_replays_walk_clean
    (k : ℕ) {σv σw : EVMState} {p ss base iv iw idx maxN cur : UInt256}
    (hclean : ((updateWalk ss base k σw iw idx maxN cur).1).hash_collision = false)
    (hmap : ∀ (I : List UInt256) (w : UInt256),
        Finmap.lookup I ((updateWalk ss base k σw iw idx maxN cur).1).keccak_map = some w →
        Finmap.lookup I σv.keccak_map = some w)
    (hjunkv : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i σv.machine_state.memory
          = Finmap.lookup i σw.machine_state.memory)
    (hlo : ∀ j : ℕ, j < k →
        96 ≤ ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32).val)
    (hhi : ∀ j : ℕ, j < k →
        ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32).val + 32 ≤ 2 ^ 256)
    (hsibs : ∀ j : ℕ, j < k →
        σv.mload ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32)
          = walkSib ss base (updateWalk ss base j σw iw idx maxN cur))
    (hv : σv.hash_collision = false) :
    ((generated.AtomicFlowManager.AtomicFlowManager.foldRoot σv p k iv idx cur).2).hash_collision
      = false := by
  rw [← (foldWalk_foldRoot k).2]
  have hflag := (fold_walk_agree k
    (σv := σv) (σw := σw) (p := p) (iv := iv) (ss := ss) (base := base)
    (iw := iw) (idx := idx) (maxN := maxN) (cur := cur)
    (fun j hj => by
      rw [foldWalk_index j, foldWalk_mload_high j (hlo j hj) (hhi j hj)]
      exact hsibs j hj)
    (fun j hj => hmap _ _ (walk_caches k hclean j hj))
    (fun j hj i hi1 hi2 => by
      rw [hjunkv i hi1 hi2, walkPreHash_junk hi1, updateWalk_junk j hi1])).2.2.2
  rw [hflag]
  exact hv

/-- **THE ROOT PINS THE WRITTEN LEAF (A6′).**  Compose the replay (#32) with
Merkle path binding (#27): if a collision-free builder walk stored root `R`
for leaf `cur` at position `idx`, and ANY challenger produces a collision-free
fold of a leaf `L` at the SAME position `idx` reaching `R` — any proof array,
any memory, any level counter — then `L` IS the written leaf `cur`.  The
committed root admits exactly one leaf per position: the one the builder
wrote.  This is what the delivery gate (#25) and reclaim gate (#26) check
against, so whatever they accept at position `idx` is the builder's leaf. -/
theorem root_pins_written_leaf
    (k : ℕ) {σv σw σc : EVMState}
    {p pc ss base iv ic iw idx maxN cur L : UInt256}
    (hclean : ((updateWalk ss base k σw iw idx maxN cur).1).hash_collision = false)
    (hmap : ∀ (I : List UInt256) (w : UInt256),
        Finmap.lookup I ((updateWalk ss base k σw iw idx maxN cur).1).keccak_map = some w →
        Finmap.lookup I σv.keccak_map = some w)
    (hjunkv : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i σv.machine_state.memory
          = Finmap.lookup i σw.machine_state.memory)
    (hlo : ∀ j : ℕ, j < k →
        96 ≤ ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32).val)
    (hhi : ∀ j : ℕ, j < k →
        ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32).val + 32 ≤ 2 ^ 256)
    (hsibs : ∀ j : ℕ, j < k →
        σv.mload ((p + Fin.shiftLeft (iv + (j : UInt256)) 5) + 32)
          = walkSib ss base (updateWalk ss base j σw iw idx maxN cur))
    (hv : σv.hash_collision = false)
    -- the challenger: a collision-free fold of `L` at position `idx`
    -- reaching the stored root
    (hcc : ((generated.AtomicFlowManager.AtomicFlowManager.foldRoot σc pc k ic idx L).2).hash_collision = false)
    (hcroot : (generated.AtomicFlowManager.AtomicFlowManager.foldRoot σc pc k ic idx L).1
        = (updateWalk ss base k σw iw idx maxN cur).2.2.2.2) :
    L = cur := by
  have hreplay := fold_replays_walk k hclean hmap hjunkv hlo hhi hsibs
  have hrclean := fold_replays_walk_clean k hclean hmap hjunkv hlo hhi hsibs hv
  exact generated.AtomicFlowManager.AtomicFlowManager.foldRoot_binding k hcc hrclean
    (by rw [hcroot, ← hreplay])

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
