import specs.KeccakDeterminism

/-!
# BUILDER/VERIFIER FOLD-DIVERGENCE attack vector (MODEL-DERIVED, AXIOM-FREE)

## The attack

Two chains run the *same* multi-level pair-hash walk over the *same* sibling
list: the **builder** computes a new Merkle root, the **verifier** replays the
walk to check it.  Each level is one EVM mapping-style pair hash
(`mstore 0 key; mstore 32 base; keccak256 0 64` — `Clear.KeccakDeterminism.accOut`),
with `base` = the running accumulator produced by the previous level.

The attacker wants the two folds to **diverge**: the verifier's final
accumulator ≠ the accumulator the builder actually committed.  A divergence is
a root the verifier accepts that the builder never produced (or vice versa), so
it is the pivot of every "accepted-but-not-committed root" story.

## What is established here

* `accValFold` — the VALUE-threading fold: unlike the pre-existing
  `accStateFold` (state only, externally supplied `(key, base)` pairs), each
  step's `base` is the PREVIOUS step's OUTPUT.  That is what a real Merkle walk
  does, so the value sequence is *self-determined* by `(start accumulator,
  sibling list)`.
* Structural lemmas: `accValFold_nil`, `accValFold_cons`, `accValFold_append`
  (phase composition, mirroring `accStateFold_append`), plus the bridge
  `accValFold_state_eq_accStateFold` showing the value fold's state component is
  literally an `accStateFold` over the pairs it generates.
* `accValFold_junk_window` / `accValFold_junk_agree` — the N-step junk-window
  frame for the value fold: an arbitrarily long walk neither disturbs nor
  depends on memory outside the scratch window `[0, 64)` at indices `≥ 64`.
* `fold_deterministic` — the headline: the verifier's fold produces EXACTLY the
  builder's final value.
* `no_fold_divergence`, `no_fold_divergence₂` — the same fact phrased as the
  attack statement.
* `accValFold_state_of_cached` — under the same hypotheses the verifier's fold
  is a pure cache walk: its post-state is the builder's *pair* sequence
  `mstore`d onto the verifier's own start state, and its keccak cache never
  grows.

## The EXACT conditions required (and why they cannot be dropped)

`fold_deterministic` needs exactly two hypotheses, both about the verifier state
`σ₂` relative to the builder state `σ₁`:

1. `hframe` — `σ₁` and `σ₂` agree on memory indices `[64, 94]`.  This is the
   "junk window": `mkInterval _ 0 64` reads the 32-byte words at byte offsets
   `0 … 63`, so the *last* word read spans bytes `[63, 95)`.  The two scratch
   `mstore`s pin bytes `[0, 64)`; bytes `[64, 95)` leak in from pre-existing
   memory and are part of the keccak preimage.  Without this the two runs hash
   *different* preimages and may legitimately differ.
2. `FoldCached σ₂.keccak_map σ₁ acc ks` — at every level of the BUILDER's walk,
   the verifier's keccak cache already maps that level's preimage to the value
   the builder got there.  This is the honest "same hash function" assumption,
   see the limitation below.  It is stated against the *initial* verifier cache
   map only, which is sound because a cache-hit `accOut` provably does not
   touch `keccak_map` — so the verifier's cache is constant for the whole
   replay.

Note what is NOT required: no cleanliness (`hash_collision = false`) assumption
about the verifier, no bound on the walk length, and no relation between the
two states' memory below 64 or at/above 95.

## The FRESHNESS LIMITATION — read this before quoting these results

Clear's keccak model is **freshness-based, not a global pure function**: an
uncached preimage draws its hash from an unused slot range
(`EVMState.keccak256`, `keccak_range.partition`), so two runs in *different*
state threads can legitimately assign *different* hashes to the *same*
preimage.  Consequently **unconditional fold determinism is FALSE in this model
and is not claimed here.**  The provable statement is CONDITIONAL on cache
agreement — hypothesis 2 above, discharged by `accOut_of_cached_frame` — which
is precisely the shape the concrete layer supplies (the verifier replays inside
a state thread that already contains the builder's cache entries, e.g. via the
`hmono` cache-monotonicity hypotheses used by
`KeccakDeterminism.accessor_chain_deterministic`).

`specs/KeccakInjective.lean` is deliberately NOT imported: it carries
trusted-base AXIOMS (`keccak256_inj`, …).  Everything below is derived from the
model — no axioms beyond the kernel's, no `sorry`.
-/

namespace AttackVectors.FoldDivergence

open Clear Clear.KeccakDeterminism EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-! ## The value-threading fold -/

/-- **The value fold.**  A multi-level pair-hash walk that threads BOTH the
running accumulator and the state: level `k` hashes the pair `(k, acc)` and the
resulting hash becomes the next level's `base`.  Returns `(final accumulator,
final state)`.

Contrast with `KeccakDeterminism.accStateFold`, which tracks only the state and
takes the `(key, base)` pairs as external data.  Here the `base` at each level
is *derived*, which is what makes the value sequence a function of
`(acc, siblings)` alone. -/
def accValFold (σ : EVMState) (acc : UInt256) : List UInt256 → UInt256 × EVMState
  | [] => (acc, σ)
  | k :: rest => accValFold (accOut σ k acc).2 (accOut σ k acc).1 rest

/-- Empty walk: nothing happens. -/
@[simp] theorem accValFold_nil (σ : EVMState) (acc : UInt256) :
    accValFold σ acc [] = (acc, σ) := rfl

/-- One level: hash `(k, acc)`, continue from the hash. -/
theorem accValFold_cons (σ : EVMState) (acc k : UInt256) (rest : List UInt256) :
    accValFold σ acc (k :: rest)
      = accValFold (accOut σ k acc).2 (accOut σ k acc).1 rest := rfl

/-- **PHASE COMPOSITION.**  Walking a concatenated sibling list is walking the
two segments in turn — the value-fold analogue of
`KeccakDeterminism.accStateFold_append`, and the shape behind splitting a real
walk into phases (update walk ++ pad ++ push walk). -/
theorem accValFold_append (σ : EVMState) (acc : UInt256) (p q : List UInt256) :
    accValFold σ acc (p ++ q)
      = accValFold (accValFold σ acc p).2 (accValFold σ acc p).1 q := by
  induction p generalizing σ acc with
  | nil => rfl
  | cons k tl ih =>
      simp only [List.cons_append, accValFold_cons]
      exact ih (accOut σ k acc).2 (accOut σ k acc).1

/-- The `(key, base)` pair sequence a value fold actually feeds to `accOut`:
each sibling paired with the accumulator current at that level. -/
def accValPairs (σ : EVMState) (acc : UInt256) : List UInt256 → List (UInt256 × UInt256)
  | [] => []
  | k :: rest =>
      (k, acc) :: accValPairs (accOut σ k acc).2 (accOut σ k acc).1 rest

/-- **BRIDGE TO `accStateFold`.**  The state component of the value fold is
exactly the pre-existing state fold run on the pairs the value fold generates —
so every `accStateFold` frame lemma transfers to `accValFold`. -/
theorem accValFold_state_eq_accStateFold :
    ∀ (ks : List UInt256) (σ : EVMState) (acc : UInt256),
      (accValFold σ acc ks).2 = accStateFold σ (accValPairs σ acc ks)
  | [], _, _ => rfl
  | k :: rest, σ, acc => by
      simp only [accValFold_cons, accValPairs, accStateFold]
      exact accValFold_state_eq_accStateFold rest (accOut σ k acc).2 (accOut σ k acc).1

/-! ## Junk-window frame for the value fold -/

/-- **N-STEP JUNK-WINDOW FRAME (value fold).**  A walk of ANY length leaves
memory at every index `i ≥ 64` untouched: the only writes are the two scratch
`mstore`s at `[0, 64)`, and `keccak256` does not write memory at all.  The value
fold's analogue of `KeccakDeterminism.accStateFold_junk_window`. -/
theorem accValFold_junk_window {i : UInt256} (hi : 64 ≤ i.val)
    (ks : List UInt256) (σ : EVMState) (acc : UInt256) :
    Finmap.lookup i (accValFold σ acc ks).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  rw [accValFold_state_eq_accStateFold, accStateFold_junk_window hi]

/-- **FOLD AGREEMENT ON THE JUNK WINDOW (value fold).**  Builder and verifier
may run walks of different length and content; if they agree at a junk index
`i ≥ 64` before, they still agree there after.  So the junk-window frame
hypothesis of `fold_deterministic` is *self-propagating* along the two folds —
which is exactly why one agreement hypothesis at the start suffices. -/
theorem accValFold_junk_agree
    {σ₁ σ₂ : EVMState} {acc₁ acc₂ : UInt256} {ks₁ ks₂ : List UInt256}
    {i : UInt256} (hi : 64 ≤ i.val)
    (h : Finmap.lookup i σ₁.machine_state.memory
      = Finmap.lookup i σ₂.machine_state.memory) :
    Finmap.lookup i (accValFold σ₁ acc₁ ks₁).2.machine_state.memory
      = Finmap.lookup i (accValFold σ₂ acc₂ ks₂).2.machine_state.memory := by
  rw [accValFold_junk_window hi, accValFold_junk_window hi]
  exact h

/-! ## The cache-agreement predicate

The one honest assumption the freshness model forces on us, made explicit. -/

/-- **CACHE AGREEMENT ALONG A WALK.**  `FoldCached m σ acc ks` says: the cache
map `m` (the verifier's) maps EVERY level-preimage of the builder's walk
(`σ`, `acc`, siblings `ks`) to EXACTLY the hash the builder obtained at that
level.

Indexed by a bare `Finmap` rather than a state on purpose: a cache-hit `accOut`
provably only `mstore`s, so the verifier's `keccak_map` is *literally* unchanged
(`rfl`) across the whole replay, and this predicate needs no re-establishing at
each induction step. -/
def FoldCached (m : Finmap (fun _ : List UInt256 => UInt256)) :
    EVMState → UInt256 → List UInt256 → Prop
  | _, _, [] => True
  | σ, acc, k :: rest =>
      Finmap.lookup (accInterval σ k acc) m = some (accOut σ k acc).1
        ∧ FoldCached m (accOut σ k acc).2 (accOut σ k acc).1 rest

@[simp] theorem FoldCached_nil (m : Finmap (fun _ : List UInt256 => UInt256))
    (σ : EVMState) (acc : UInt256) : FoldCached m σ acc [] := trivial

theorem FoldCached_cons_iff {m : Finmap (fun _ : List UInt256 => UInt256)}
    {σ : EVMState} {acc k : UInt256} {rest : List UInt256} :
    FoldCached m σ acc (k :: rest)
      ↔ Finmap.lookup (accInterval σ k acc) m = some (accOut σ k acc).1
        ∧ FoldCached m (accOut σ k acc).2 (accOut σ k acc).1 rest := Iff.rfl

/-- Cache agreement splits along a phase decomposition, mirroring
`accValFold_append`. -/
theorem FoldCached_append {m : Finmap (fun _ : List UInt256 => UInt256)} :
    ∀ (p q : List UInt256) (σ : EVMState) (acc : UInt256),
      FoldCached m σ acc (p ++ q)
        ↔ FoldCached m σ acc p
          ∧ FoldCached m (accValFold σ acc p).2 (accValFold σ acc p).1 q
  | [], _, _, _ => by simp only [List.nil_append, accValFold_nil, FoldCached_nil,
      true_and]
  | k :: tl, q, σ, acc => by
      simp only [List.cons_append, FoldCached_cons_iff, accValFold_cons,
        FoldCached_append tl q (accOut σ k acc).2 (accOut σ k acc).1, and_assoc]

/-! ## Divergence is impossible -/

/-- Auxiliary: under cache agreement the verifier's fold is a **pure cache
walk** — every level is a hit, the final value is the builder's final value,
and the verifier's post-state is its own start state with the builder's pair
sequence `mstore`d into scratch (in particular its `keccak_map` never grows). -/
theorem accValFold_state_of_cached :
    ∀ (ks : List UInt256) (σ₁ σ₂ : EVMState) (acc : UInt256)
      (_hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
        Finmap.lookup i σ₁.machine_state.memory
          = Finmap.lookup i σ₂.machine_state.memory)
      (_hcache : FoldCached σ₂.keccak_map σ₁ acc ks),
      accValFold σ₂ acc ks
        = ((accValFold σ₁ acc ks).1,
           accStateFold σ₂ (accValPairs σ₁ acc ks))
  | [], _, _, _, _, _ => rfl
  | k :: rest, σ₁, σ₂, acc, hframe, hcache => by
      -- The verifier hits the cache at this level, returning the builder's hash.
      have hhit : accOut σ₂ k acc
          = ((accOut σ₁ k acc).1, (σ₂.mstore 0 k).mstore 32 acc) :=
        accOut_of_cached_frame hframe hcache.1
      -- The junk window survives on both sides, so the frame hypothesis persists.
      have hframe' : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
          Finmap.lookup i (accOut σ₁ k acc).2.machine_state.memory
            = Finmap.lookup i ((σ₂.mstore 0 k).mstore 32 acc).machine_state.memory := by
        intro i h1 h2
        rw [accOut_junk_window h1]
        rw [show ((σ₂.mstore 0 k).mstore 32 acc) = (accOut σ₂ k acc).2 from
          by rw [hhit]]
        rw [accOut_junk_window h1]
        exact hframe i h1 h2
      -- `mstore` does not touch the keccak cache, so the predicate carries over.
      have hmap : ((σ₂.mstore 0 k).mstore 32 acc).keccak_map = σ₂.keccak_map := rfl
      have hcache' : FoldCached ((σ₂.mstore 0 k).mstore 32 acc).keccak_map
          (accOut σ₁ k acc).2 (accOut σ₁ k acc).1 rest := by
        rw [hmap]; exact hcache.2
      simp only [accValFold_cons, accValPairs, accStateFold, hhit]
      rw [accValFold_state_of_cached rest (accOut σ₁ k acc).2
        ((σ₂.mstore 0 k).mstore 32 acc) (accOut σ₁ k acc).1 hframe' hcache']

/-- **FOLD DETERMINISM (headline).**  The verifier's multi-level pair-hash walk
produces EXACTLY the builder's final accumulator, given:

* `hframe` — builder and verifier states agree on memory bytes `[64, 94]`, the
  part of the 64-byte keccak preimage the two scratch `mstore`s do NOT
  overwrite; and
* `hcache` — at every level of the builder's walk, the verifier's keccak cache
  already maps that level's preimage to the builder's hash there.

Nothing else: no cleanliness assumption on the verifier, no length bound, no
agreement anywhere else in memory.  See the file header on why hypothesis 2 is
unavoidable in Clear's freshness-based keccak model.  Axiom-free. -/
theorem fold_deterministic
    {σ₁ σ₂ : EVMState} {acc : UInt256} {ks : List UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory)
    (hcache : FoldCached σ₂.keccak_map σ₁ acc ks) :
    (accValFold σ₂ acc ks).1 = (accValFold σ₁ acc ks).1 := by
  rw [accValFold_state_of_cached ks σ₁ σ₂ acc hframe hcache]

/-- **NO BUILDER/VERIFIER FOLD DIVERGENCE.**  The attack statement: an attacker
cannot exhibit a verifier state that satisfies the agreement conditions yet
whose replay of the SAME sibling list from the SAME start accumulator lands on a
DIFFERENT root than the builder committed. -/
theorem no_fold_divergence
    {σ₁ σ₂ : EVMState} {acc : UInt256} {ks : List UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory)
    (hcache : FoldCached σ₂.keccak_map σ₁ acc ks) :
    ¬ ((accValFold σ₂ acc ks).1 ≠ (accValFold σ₁ acc ks).1) :=
  fun hne => hne (fold_deterministic hframe hcache)

/-- **NO DIVERGENCE BETWEEN TWO VERIFIERS.**  Two independent replaying chains
that both satisfy the agreement conditions against the same builder walk cannot
accept different roots — the multi-verifier form of the attack. -/
theorem no_fold_divergence₂
    {σ₁ σ₂ σ₃ : EVMState} {acc : UInt256} {ks : List UInt256}
    (hframe₂ : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory)
    (hcache₂ : FoldCached σ₂.keccak_map σ₁ acc ks)
    (hframe₃ : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₃.machine_state.memory)
    (hcache₃ : FoldCached σ₃.keccak_map σ₁ acc ks) :
    ¬ ((accValFold σ₂ acc ks).1 ≠ (accValFold σ₃ acc ks).1) := by
  intro hne
  exact hne ((fold_deterministic hframe₂ hcache₂).trans
    (fold_deterministic hframe₃ hcache₃).symm)

/-- **PHASE-COMPOSED DETERMINISM.**  Determinism survives splitting the walk
into phases: agreement on the first phase pins the intermediate accumulator,
and agreement on the second (starting from the builder's phase-1 post-state)
pins the root.  The form a concrete "update walk ++ push walk" proof consumes. -/
theorem fold_deterministic_phases
    {σ₁ σ₂ : EVMState} {acc : UInt256} {p q : List UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory)
    (hp : FoldCached σ₂.keccak_map σ₁ acc p)
    (hq : FoldCached σ₂.keccak_map (accValFold σ₁ acc p).2
      (accValFold σ₁ acc p).1 q) :
    (accValFold σ₂ acc (p ++ q)).1 = (accValFold σ₁ acc (p ++ q)).1 :=
  fold_deterministic hframe ((FoldCached_append p q σ₁ acc).mpr ⟨hp, hq⟩)

end AttackVectors.FoldDivergence
