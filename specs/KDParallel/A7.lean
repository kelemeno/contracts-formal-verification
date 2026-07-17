import Clear.EVMState
import specs.KeccakDeterminism

/-!
# Composite `accOut`-step frame lemmas (KDParallel A7)

Packaged frame facts for a *single* `accOut` accessor step (scratch writes at
`[0, 64)` followed by the 64-byte keccak) and for a *two-step* cross-state
agreement, all built on top of `specs.KeccakDeterminism`:

* `accOut_preserves_high_and_junk` — one step preserves BOTH the byte-level junk
  window (`64 ≤ i.val`, from `accOut_junk_window`) AND the word-level high region
  (`96 ≤ a.val`, from `accOut_mload_high`); a genuine composite of the two frames.
* `accOut_keccak_map_after_mstore` — one step never drops keccak-cache entries,
  neither through the two scratch `mstore`s (`keccak_map_mstore`) nor through the
  keccak PRIMOP (`accOut_lookup_mono`); the cache only grows.
* `accOut_agree_value₂` — a 2-level cross-state agreement: if `σ₂` agrees with
  `σ₁` on the junk window and caches BOTH the level-0 preimage and the level-1
  preimage (the one produced after one honest `accOut` on `σ₁`), then the two
  cross-state `accOut` values equal the honest ones. The frame is carried from
  level 0 to level 1 through `accOut_junk_window`.

Axiom-free (derived entirely from the model, like the parent module).
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- **One-step high + junk frame.**  A single `accOut` step preserves both the
byte-level junk window (`64 ≤ i.val`) and the word-level high region
(`96 ≤ a.val`, non-wrapping): the two scratch `mstore`s write only `[0, 64)` and
the keccak PRIMOP does not touch memory.  Composite of `accOut_junk_window` and
`accOut_mload_high`. -/
theorem accOut_preserves_high_and_junk
    {σ : EVMState} {key base : UInt256}
    {i : UInt256} (hi : 64 ≤ i.val)
    {a : UInt256} (ha : 96 ≤ a.val) (hnw : a.val + 32 ≤ 2 ^ 256) :
    Finmap.lookup i (accOut σ key base).2.machine_state.memory
        = Finmap.lookup i σ.machine_state.memory
    ∧ (accOut σ key base).2.mload a = σ.mload a :=
  ⟨accOut_junk_window hi, accOut_mload_high ha hnw⟩

/-- **One-step cache monotonicity.**  A single `accOut` step never drops a
keccak-cache entry: an entry present in `σ.keccak_map` survives both through the
two scratch `mstore`s (whose `keccak_map` is definitionally `σ`'s) and through
the full step's post-state.  Composite of `keccak_map_mstore` and
`accOut_lookup_mono`. -/
theorem accOut_keccak_map_after_mstore
    {σ : EVMState} {key base : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (accOut σ key base).2.keccak_map = some w
    ∧ Finmap.lookup I ((σ.mstore 0 key).mstore 32 base).keccak_map = some w := by
  refine ⟨accOut_lookup_mono hI, ?_⟩
  rw [keccak_map_mstore, keccak_map_mstore]
  exact hI

/-- **2-level cross-state accessor agreement.**  Let the honest run apply
`accOut _ k₁ b₁` (level 0) and then `accOut _ k₂ b₂` (level 1).  If the cross
state `σ₂` agrees with `σ₁` on the junk window `[64, 95)` and caches BOTH

* the level-0 preimage `accInterval σ₁ k₁ b₁`, mapped to the honest level-0 hash,
  and
* the level-1 preimage `accInterval (accOut σ₁ k₁ b₁).2 k₂ b₂`, mapped to the
  honest level-1 hash,

then the two cross-state `accOut` values equal the honest ones.  The junk-window
frame is carried from level 0 to level 1 via `accOut_junk_window` (the two
scratch `mstore`s and the keccak PRIMOP leave `[64, 95)` intact), so no
cleanliness assumption on either run is needed — both levels hit the cache.
Axiom-free. -/
theorem accOut_agree_value₂
    {σ₁ σ₂ : EVMState} {k₁ b₁ k₂ b₂ : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory)
    (hc0 : Finmap.lookup (accInterval σ₁ k₁ b₁) σ₂.keccak_map
        = some (accOut σ₁ k₁ b₁).1)
    (hc1 : Finmap.lookup (accInterval (accOut σ₁ k₁ b₁).2 k₂ b₂) σ₂.keccak_map
        = some (accOut (accOut σ₁ k₁ b₁).2 k₂ b₂).1) :
    (accOut σ₂ k₁ b₁).1 = (accOut σ₁ k₁ b₁).1
    ∧ (accOut (accOut σ₂ k₁ b₁).2 k₂ b₂).1
        = (accOut (accOut σ₁ k₁ b₁).2 k₂ b₂).1 := by
  -- Level 0: the cross-state step hits the cache and returns the honest hash.
  have hv0 : (accOut σ₂ k₁ b₁).1 = (accOut σ₁ k₁ b₁).1 :=
    accOut_agree_value hframe hc0
  -- Its post-evm is exactly the double-`mstore`d `σ₂` (cache hit).
  have he2 : (accOut σ₂ k₁ b₁).2 = (σ₂.mstore 0 k₁).mstore 32 b₁ := by
    rw [accOut_of_cached_frame hframe hc0]
  -- Level 1: carry the junk-window frame across both level-0 post-states.
  have hframe1 : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i (accOut σ₁ k₁ b₁).2.machine_state.memory
        = Finmap.lookup i (accOut σ₂ k₁ b₁).2.machine_state.memory := by
    intro i hi hi'
    exact (accOut_junk_window (σ := σ₁) (key := k₁) (base := b₁) hi).trans
      ((hframe i hi hi').trans
        (accOut_junk_window (σ := σ₂) (key := k₁) (base := b₁) hi).symm)
  -- The level-1 preimage is cached in the level-0 cross post-state (its cache is
  -- `σ₂`'s, unchanged by the two scratch `mstore`s).
  have hc1' : Finmap.lookup (accInterval (accOut σ₁ k₁ b₁).2 k₂ b₂)
        (accOut σ₂ k₁ b₁).2.keccak_map
      = some (accOut (accOut σ₁ k₁ b₁).2 k₂ b₂).1 := by
    rw [he2, keccak_map_mstore, keccak_map_mstore]
    exact hc1
  have hv1 : (accOut (accOut σ₂ k₁ b₁).2 k₂ b₂).1
      = (accOut (accOut σ₁ k₁ b₁).2 k₂ b₂).1 :=
    accOut_agree_value hframe1 hc1'
  exact ⟨hv0, hv1⟩

end Clear.KeccakDeterminism
