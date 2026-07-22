import Clear.EVMState
import specs.KeccakDeterminism

/-!
# The n-step accessor-fold agreement (KDParallel)

Generalizes the 2-level atoms (`accOut_junk_window₂`, `accOut_agree_value₂`) to
a fold of ARBITRARY depth by induction.  `accFold` runs a chain of `accOut`
steps in which each level's `(key, base)` pair is an arbitrary function of the
RUNNING VALUE — covering both the nested-mapping accessor chain (the base is
threaded) and the multi-level Merkle pair-hash fold (the running hash sits on
either side of the sibling, per path parity).

* `accFold_junk_window` — the junk window `[64, 95)` survives any depth.
* `accFold_lookup_mono` / `accFold_clean_backward` — the keccak cache only
  grows along a fold, and a collision-free end-state forces a collision-free
  start state.
* `accFold_caches_of_clean` — a collision-free honest fold caches EVERY level's
  preimage interval, mapped to that level's hash.
* `accFold_agree` — THE INDUCTION: a cross state that agrees on the junk window
  and carries every honest level's cache entry folds to the SAME final value.
  The cross run hits the cache at every level, so the threaded running value
  stays synchronized and both runs present identical preimages at the next
  level; no cleanliness assumption on the cross run is needed.
* `accFold_deterministic` — capstone: honest run collision-free + cache
  transport ⇒ the cross fold returns the honest value.  The n-level
  builder–verifier fold agreement, fully abstract.

Axiom-free (derived entirely from the model, like the parent module).
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- The dependent accessor fold: at each level, the step's `(key, base)` is an
arbitrary function `f` of the running value, and the step's hash becomes the
new running value.  `(accFold σ v fs).1` is the final value, `.2` the final
evm.  Merkle instance: `f cur = (cur, sib)` or `(sib, cur)` per path parity;
nested-mapping instance: `f cur = (key, cur)`. -/
def accFold (σ : EVMState) (v : UInt256) :
    List (UInt256 → UInt256 × UInt256) → UInt256 × EVMState
  | [] => (v, σ)
  | f :: rest =>
      accFold (accOut σ (f v).1 (f v).2).2 (accOut σ (f v).1 (f v).2).1 rest

/-- The honest run's per-level cache footprint: each level's keccak preimage
interval, mapped to that level's hash. -/
def accFoldCaches (σ : EVMState) (v : UInt256) :
    List (UInt256 → UInt256 × UInt256) → List (List UInt256 × UInt256)
  | [] => []
  | f :: rest =>
      (accInterval σ (f v).1 (f v).2, (accOut σ (f v).1 (f v).2).1)
        :: accFoldCaches (accOut σ (f v).1 (f v).2).2 (accOut σ (f v).1 (f v).2).1 rest

private theorem accFold_junk_window_aux
    (fs : List (UInt256 → UInt256 × UInt256)) {i : UInt256} (hi : 64 ≤ i.val) :
    ∀ (σ : EVMState) (v : UInt256),
      Finmap.lookup i (accFold σ v fs).2.machine_state.memory
        = Finmap.lookup i σ.machine_state.memory := by
  induction fs with
  | nil => intro σ v; rfl
  | cons f rest ih =>
    intro σ v
    simp only [accFold]
    exact (ih _ _).trans
      (accOut_junk_window (σ := σ) (key := (f v).1) (base := (f v).2) hi)

/-- **n-step junk window.**  The junk window `[64, 95)` survives an accessor
fold of any depth — every step writes only the scratch `[0, 64)` and the keccak
PRIMOP does not touch memory.  Generalizes `accOut_junk_window₂`. -/
theorem accFold_junk_window
    {σ : EVMState} {v : UInt256} {fs : List (UInt256 → UInt256 × UInt256)}
    {i : UInt256} (hi : 64 ≤ i.val) :
    Finmap.lookup i (accFold σ v fs).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory :=
  accFold_junk_window_aux fs hi σ v

private theorem accFold_lookup_mono_aux
    (fs : List (UInt256 → UInt256 × UInt256)) {I : List UInt256} {w : UInt256} :
    ∀ (σ : EVMState) (v : UInt256),
      Finmap.lookup I σ.keccak_map = some w →
        Finmap.lookup I (accFold σ v fs).2.keccak_map = some w := by
  induction fs with
  | nil => intro σ _ hI; exact hI
  | cons f rest ih =>
    intro σ v hI
    simp only [accFold]
    exact ih _ _ (accOut_lookup_mono hI)

/-- **n-step cache monotonicity.**  A keccak-cache entry survives an accessor
fold of any depth — the cache only grows. -/
theorem accFold_lookup_mono
    {σ : EVMState} {v : UInt256} {fs : List (UInt256 → UInt256 × UInt256)}
    {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (accFold σ v fs).2.keccak_map = some w :=
  accFold_lookup_mono_aux fs σ v hI

private theorem accFold_clean_backward_aux
    (fs : List (UInt256 → UInt256 × UInt256)) :
    ∀ (σ : EVMState) (v : UInt256),
      (accFold σ v fs).2.hash_collision = false → σ.hash_collision = false := by
  induction fs with
  | nil => intro σ v h; exact h
  | cons f rest ih =>
    intro σ v h
    simp only [accFold] at h
    exact accOut_clean_backward (ih _ _ h)

/-- **n-step backward cleanliness.**  A collision-free fold end-state forces a
collision-free start state. -/
theorem accFold_clean_backward
    {σ : EVMState} {v : UInt256} {fs : List (UInt256 → UInt256 × UInt256)}
    (h : (accFold σ v fs).2.hash_collision = false) :
    σ.hash_collision = false :=
  accFold_clean_backward_aux fs σ v h

private theorem accFold_caches_of_clean_aux
    (fs : List (UInt256 → UInt256 × UInt256)) :
    ∀ (σ : EVMState) (v : UInt256),
      (accFold σ v fs).2.hash_collision = false →
        ∀ p ∈ accFoldCaches σ v fs,
          Finmap.lookup p.1 (accFold σ v fs).2.keccak_map = some p.2 := by
  induction fs with
  | nil =>
    intro σ v _ p hp
    simp only [accFoldCaches] at hp
    exact absurd hp (List.not_mem_nil p)
  | cons f rest ih =>
    intro σ v hclean p hp
    simp only [accFoldCaches] at hp
    simp only [accFold] at hclean ⊢
    rcases List.mem_cons.mp hp with rfl | hp'
    · -- head entry: the level-0 step is clean (backward from the fold), so it
      -- caches its preimage, and the rest of the fold never drops the entry
      have hstep : (accOut σ (f v).1 (f v).2).2.hash_collision = false :=
        accFold_clean_backward_aux rest _ _ hclean
      exact accFold_lookup_mono_aux rest _ _ (accOut_caches_of_clean hstep)
    · exact ih _ _ hclean p hp'

/-- **A clean honest fold caches every level.**  Each level's preimage interval
is cached in the fold's end-state, mapped to that level's hash: the level's own
step caches it (`accOut_caches_of_clean`, cleanliness propagated backward), and
the remaining levels never drop it (`accFold_lookup_mono`). -/
theorem accFold_caches_of_clean
    {σ : EVMState} {v : UInt256} {fs : List (UInt256 → UInt256 × UInt256)}
    (hclean : (accFold σ v fs).2.hash_collision = false) :
    ∀ p ∈ accFoldCaches σ v fs,
      Finmap.lookup p.1 (accFold σ v fs).2.keccak_map = some p.2 :=
  accFold_caches_of_clean_aux fs σ v hclean

private theorem accFold_agree_aux
    (fs : List (UInt256 → UInt256 × UInt256)) :
    ∀ (σ₁ σ₂ : EVMState) (v : UInt256),
      (∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i σ₁.machine_state.memory
          = Finmap.lookup i σ₂.machine_state.memory) →
      (∀ p ∈ accFoldCaches σ₁ v fs,
        Finmap.lookup p.1 σ₂.keccak_map = some p.2) →
      (accFold σ₂ v fs).1 = (accFold σ₁ v fs).1 := by
  induction fs with
  | nil => intro σ₁ σ₂ v _ _; rfl
  | cons f rest ih =>
    intro σ₁ σ₂ v hframe hcache
    simp only [accFold]
    -- level 0: the cross step hits the honest cache entry and returns the
    -- honest hash — the running values stay synchronized
    have hc0 : Finmap.lookup (accInterval σ₁ (f v).1 (f v).2) σ₂.keccak_map
        = some (accOut σ₁ (f v).1 (f v).2).1 :=
      hcache (accInterval σ₁ (f v).1 (f v).2, (accOut σ₁ (f v).1 (f v).2).1)
        (by simp only [accFoldCaches]; exact List.mem_cons_self _ _)
    have hv0 : (accOut σ₂ (f v).1 (f v).2).1 = (accOut σ₁ (f v).1 (f v).2).1 :=
      accOut_agree_value hframe hc0
    -- the junk-window frame carries across both level-0 post-states
    have hframe' : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i (accOut σ₁ (f v).1 (f v).2).2.machine_state.memory
          = Finmap.lookup i (accOut σ₂ (f v).1 (f v).2).2.machine_state.memory := by
      intro i hi hi'
      exact (accOut_junk_window (σ := σ₁) (key := (f v).1) (base := (f v).2) hi).trans
        ((hframe i hi hi').trans
          (accOut_junk_window (σ := σ₂) (key := (f v).1) (base := (f v).2) hi).symm)
    -- the remaining honest cache entries survive the cross level-0 step
    have hcache' : ∀ p ∈ accFoldCaches (accOut σ₁ (f v).1 (f v).2).2
          (accOut σ₁ (f v).1 (f v).2).1 rest,
        Finmap.lookup p.1 (accOut σ₂ (f v).1 (f v).2).2.keccak_map = some p.2 := by
      intro p hp
      exact accOut_lookup_mono
        (hcache p (by simp only [accFoldCaches]; exact List.mem_cons_of_mem _ hp))
    rw [hv0]
    exact ih _ _ _ hframe' hcache'

/-- **THE n-STEP FOLD AGREEMENT.**  If the cross state `σ₂` agrees with the
honest start state `σ₁` on the junk window `[64, 95)` and carries every honest
level's cache entry (`accFoldCaches σ₁ v fs`), then the cross fold returns the
honest final value — at every level the cross run hits the cache, so the
threaded running value stays synchronized and both runs present identical
preimages at the next level.  No cleanliness assumption on the cross run.
Generalizes `accOut_agree_value₂` to arbitrary depth. -/
theorem accFold_agree
    {σ₁ σ₂ : EVMState} {v : UInt256} {fs : List (UInt256 → UInt256 × UInt256)}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory)
    (hcache : ∀ p ∈ accFoldCaches σ₁ v fs,
      Finmap.lookup p.1 σ₂.keccak_map = some p.2) :
    (accFold σ₂ v fs).1 = (accFold σ₁ v fs).1 :=
  accFold_agree_aux fs σ₁ σ₂ v hframe hcache

/-- **n-STEP FOLD DETERMINISM (capstone).**  An honest collision-free fold plus
cache transport into the cross state pins the cross fold's value: the honest
run caches every level (`accFold_caches_of_clean`), the transport carries the
entries to `σ₂`, and the agreement induction (`accFold_agree`) replays the fold
value.  The n-level builder–verifier agreement — `accessor_chain_deterministic`
for arbitrary depth and arbitrary per-level `(key, base)` dependence.  -/
theorem accFold_deterministic
    {σ₁ σ₂ : EVMState} {v : UInt256} {fs : List (UInt256 → UInt256 × UInt256)}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I (accFold σ₁ v fs).2.keccak_map = some w →
        Finmap.lookup I σ₂.keccak_map = some w)
    (hclean : (accFold σ₁ v fs).2.hash_collision = false) :
    (accFold σ₂ v fs).1 = (accFold σ₁ v fs).1 :=
  accFold_agree hframe
    (fun p hp => hmono _ _ (accFold_caches_of_clean hclean p hp))

end Clear.KeccakDeterminism
