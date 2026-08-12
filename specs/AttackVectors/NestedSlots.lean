import specs.AttackVectors.NoCrossLeg

/-
  THREE-LEVEL SLOT SEPARATION — the withdrawal-finalized mapping.

  `AttackVectors.NoCrossLeg` separates the two-level `_state[flowId][bundleHash]`.  The L1Nullifier's
  replay protection uses a THREE-level mapping,

      isWithdrawalFinalized[chainId][l2BatchNumber][l2MessageIndex]

  and its `no_replay` results (`replay_after_set_reverts`, `check_set_slots_eq`) are about ONE
  withdrawal's slot: they say a withdrawal cannot be replayed at its own slot.  As with bundles and
  legs before, that leaves the cross-withdrawal question — whether finalizing one withdrawal can mark
  a DIFFERENT one finalized (blocking a legitimate withdrawal) or clear one (enabling a replay, which
  is a drain).

  Three levels is one more step of the same argument: `CachedHashInj.accInterval_inj` returns both
  components of each preimage, so equal final slots force equal `index` and equal second
  intermediates, those force equal `batch` and equal first intermediates, and those force equal
  `chainId`.  A difference at ANY of the three coordinates propagates outward.  Axiom-free.
-/

namespace AttackVectors.NestedSlots

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.CachedHashInj

/-- **THREE-LEVEL SEPARATION.**  Two withdrawals whose `(chainId, batch, index)` triples differ in ANY
coordinate land on different storage slots, given every accessor step has been hashed. -/
theorem triple_slot_ne {σ : EVMState} (hinj : CacheInj σ)
    {c₁ c₂ n₁ n₂ x₁ x₂ base p₁ p₂ q₁ q₂ r₁ r₂ : UInt256}
    -- level 1: chainId over the mapping base
    (hp₁ : Finmap.lookup (accInterval σ c₁ base) σ.keccak_map = some p₁)
    (hp₂ : Finmap.lookup (accInterval σ c₂ base) σ.keccak_map = some p₂)
    -- level 2: batch number over the first intermediate
    (hq₁ : Finmap.lookup (accInterval σ n₁ p₁) σ.keccak_map = some q₁)
    (hq₂ : Finmap.lookup (accInterval σ n₂ p₂) σ.keccak_map = some q₂)
    -- level 3: message index over the second intermediate
    (hr₁ : Finmap.lookup (accInterval σ x₁ q₁) σ.keccak_map = some r₁)
    (hr₂ : Finmap.lookup (accInterval σ x₂ q₂) σ.keccak_map = some r₂)
    (hne : c₁ ≠ c₂ ∨ n₁ ≠ n₂ ∨ x₁ ≠ x₂) : r₁ ≠ r₂ := by
  intro he
  -- outermost: equal slots ⇒ equal index and equal second intermediate
  obtain ⟨hx, hq⟩ := accInterval_inj (hinj _ _ r₁ hr₁ (he ▸ hr₂))
  rcases hne with hc | hn | hx' 
  · -- chainId differs: peel two levels
    obtain ⟨_, hp⟩ := accInterval_inj (hinj _ _ q₁ hq₁ (hq ▸ hq₂))
    exact hc (accInterval_inj (hinj _ _ p₁ hp₁ (hp ▸ hp₂))).1
  · -- batch differs: peel one level
    exact hn (accInterval_inj (hinj _ _ q₁ hq₁ (hq ▸ hq₂))).1
  · exact hx' hx

/-- **NO CROSS-WITHDRAWAL INTERFERENCE.**  Finalizing one withdrawal leaves a different withdrawal's
flag exactly as it was — so a finalization cannot be forged sideways (blocking a legitimate
withdrawal) nor cleared (enabling a replay, which is a drain). -/
theorem finalize_frames_other_withdrawal {σ σ_w : EVMState} (hinj : CacheInj σ)
    {c₁ c₂ n₁ n₂ x₁ x₂ base p₁ p₂ q₁ q₂ r₁ r₂ v : UInt256}
    (hp₁ : Finmap.lookup (accInterval σ c₁ base) σ.keccak_map = some p₁)
    (hp₂ : Finmap.lookup (accInterval σ c₂ base) σ.keccak_map = some p₂)
    (hq₁ : Finmap.lookup (accInterval σ n₁ p₁) σ.keccak_map = some q₁)
    (hq₂ : Finmap.lookup (accInterval σ n₂ p₂) σ.keccak_map = some q₂)
    (hr₁ : Finmap.lookup (accInterval σ x₁ q₁) σ.keccak_map = some r₁)
    (hr₂ : Finmap.lookup (accInterval σ x₂ q₂) σ.keccak_map = some r₂)
    (hne : c₁ ≠ c₂ ∨ n₁ ≠ n₂ ∨ x₁ ≠ x₂) :
    (σ_w.sstore r₁ v).sload r₂ = σ_w.sload r₂ :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w
    (Ne.symm (triple_slot_ne hinj hp₁ hp₂ hq₁ hq₂ hr₁ hr₂ hne))

/-- **A DIFFERENT BATCH IS NOT FINALIZED.**  The specialization that matters for replay across
batches: same chain, same message index, different batch number.

Worth stating separately because it is the coordinate an attacker controls most cheaply — resubmitting
the same message index under a neighbouring batch. -/
theorem finalize_frames_other_batch {σ σ_w : EVMState} (hinj : CacheInj σ)
    {c n₁ n₂ x base p q₁ q₂ r₁ r₂ v : UInt256}
    (hp : Finmap.lookup (accInterval σ c base) σ.keccak_map = some p)
    (hq₁ : Finmap.lookup (accInterval σ n₁ p) σ.keccak_map = some q₁)
    (hq₂ : Finmap.lookup (accInterval σ n₂ p) σ.keccak_map = some q₂)
    (hr₁ : Finmap.lookup (accInterval σ x q₁) σ.keccak_map = some r₁)
    (hr₂ : Finmap.lookup (accInterval σ x q₂) σ.keccak_map = some r₂)
    (hn : n₁ ≠ n₂) :
    (σ_w.sstore r₁ v).sload r₂ = σ_w.sload r₂ :=
  finalize_frames_other_withdrawal hinj hp hp hq₁ hq₂ hr₁ hr₂ (Or.inr (Or.inl hn))

/-! ## THE GENERAL n-LEVEL FORM

Bundles (one level), legs (two) and withdrawals (three) all took the same argument, unchanged at each
depth.  That is the signal to state it once.  `nestedSlot` folds the accessor over a list of keys,
threading each intermediate as the next base — Solidity's `m[k₁][k₂]…[kₙ]`.

The three concrete results above are kept rather than replaced: they are the shapes callers actually
have, and rederiving them through the general form would add a list-manipulation step at every use for
no gain in strength. -/

/-- The slot of a nested mapping at `keys` over `base`, threading each intermediate as the next base. -/
def nestedSlot (σ : EVMState) (base : UInt256) : List UInt256 → UInt256
  | [] => base
  | k :: ks => nestedSlot σ (accOut σ k base).1 ks

/-- Every accessor step along the way has been hashed. -/
def NestedCached (σ : EVMState) (base : UInt256) : List UInt256 → Prop
  | [] => True
  | k :: ks =>
      (∃ r, Finmap.lookup (accInterval σ k base) σ.keccak_map = some r)
        ∧ NestedCached σ (accOut σ k base).1 ks

/-- **n-LEVEL SEPARATION.**  Two nested lookups of the same depth landing on the same slot have the
same keys AND the same base — so any difference in any coordinate separates them.

The base is concluded equal rather than assumed, which is what makes the induction go through: peeling
one level turns a statement about keys into a statement about the intermediates, and those are bases. -/
theorem nestedSlot_inj {σ : EVMState} (hinj : CacheInj σ) :
    ∀ (ks₁ ks₂ : List UInt256) (b₁ b₂ : UInt256),
      ks₁.length = ks₂.length →
      NestedCached σ b₁ ks₁ → NestedCached σ b₂ ks₂ →
      nestedSlot σ b₁ ks₁ = nestedSlot σ b₂ ks₂ →
      ks₁ = ks₂ ∧ b₁ = b₂ := by
  intro ks₁
  induction ks₁ with
  | nil =>
    intro ks₂ b₁ b₂ hlen _ _ heq
    cases ks₂ with
    | nil => exact ⟨rfl, heq⟩
    | cons _ _ => simp at hlen
  | cons k₁ rest ih =>
    intro ks₂ b₁ b₂ hlen hc₁ hc₂ heq
    cases ks₂ with
    | nil => simp at hlen
    | cons k₂ rest₂ =>
      obtain ⟨⟨r₁, hr₁⟩, hrest₁⟩ := hc₁
      obtain ⟨⟨r₂, hr₂⟩, hrest₂⟩ := hc₂
      have hlen' : rest.length = rest₂.length := by simpa using hlen
      obtain ⟨hks, hb⟩ := ih rest₂ _ _ hlen' hrest₁ hrest₂ heq
      -- the intermediates agree, so the first steps' preimages do
      have hv₁ : (accOut σ k₁ b₁).1 = r₁ := by rw [accOut_of_cached hr₁]
      have hv₂ : (accOut σ k₂ b₂).1 = r₂ := by rw [accOut_of_cached hr₂]
      rw [hv₁, hv₂] at hb
      obtain ⟨hk, hbb⟩ := accInterval_inj (hinj _ _ r₁ hr₁ (hb ▸ hr₂))
      exact ⟨by rw [hk, hks], hbb⟩

/-- **THE FRAME, n-LEVEL.**  A write at one nested slot is invisible at another of the same depth
whose key list differs. -/
theorem nested_write_frames {σ σ_w : EVMState} (hinj : CacheInj σ)
    {b : UInt256} {ks₁ ks₂ : List UInt256} {v : UInt256}
    (hlen : ks₁.length = ks₂.length)
    (hc₁ : NestedCached σ b ks₁) (hc₂ : NestedCached σ b ks₂)
    (hne : ks₁ ≠ ks₂) :
    (σ_w.sstore (nestedSlot σ b ks₁) v).sload (nestedSlot σ b ks₂)
      = σ_w.sload (nestedSlot σ b ks₂) :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w
    (fun he => hne (nestedSlot_inj hinj ks₁ ks₂ b b hlen hc₁ hc₂ he.symm).1)

/-! ## THE UNSEEN KEY AT ARBITRARY DEPTH

The n-level separation above needs every step cached.  The remaining case — a nested lookup whose LAST
step has never been hashed — is again freshness rather than injectivity, and it needs no new argument:
`KeccakFresh.keccakOut_miss_fresh` takes an ARBITRARY cached interval, so the cached slot it is compared
against need not belong to the same mapping — which matters here, since a nested entry can collide with
anything.  `NoCrossLeg.fresh_leg_slot_ne_cached` is the same shape one level down.

(`NoCrossBundle.fresh_slot_ne_cached` does NOT generalize here: it fixes both keys to a common base.) -/

/-- **A NEVER-COMPUTED NESTED SLOT IS FRESH.**  If the last accessor step of a nested lookup is not in
the cache, its slot differs from every cached slot — at any depth. -/
theorem fresh_nestedSlot_ne_cached {σ : EVMState} (hinv : CacheInUsed σ)
    {b k r : UInt256} {ks : List UInt256} {I : List UInt256}
    {used : List UInt256} {hd : UInt256} {tl : List UInt256}
    (hc : Finmap.lookup I σ.keccak_map = some r)
    (hmiss : Finmap.lookup (accInterval σ k (nestedSlot σ b ks)) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl)) :
    (accOut σ k (nestedSlot σ b ks)).1 ≠ r :=
  Clear.KeccakFresh.keccakOut_miss_fresh
    (σ := (σ.mstore 0 k).mstore 32 (nestedSlot σ b ks))
    (Clear.KeccakFresh.cacheInUsed_mstore 32 (nestedSlot σ b ks)
      (Clear.KeccakFresh.cacheInUsed_mstore 0 k hinv))
    hmiss hpart hc

/-- **NO INTERFERENCE WITH AN UNSEEN NESTED ENTRY.**  A write at any cached slot is invisible at the
slot a never-computed nested entry draws. -/
theorem nested_write_frames_fresh {σ σ_w : EVMState} (hinv : CacheInUsed σ)
    {b k r v : UInt256} {ks : List UInt256} {I : List UInt256}
    {used : List UInt256} {hd : UInt256} {tl : List UInt256}
    (hc : Finmap.lookup I σ.keccak_map = some r)
    (hmiss : Finmap.lookup (accInterval σ k (nestedSlot σ b ks)) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl)) :
    (σ_w.sstore r v).sload (accOut σ k (nestedSlot σ b ks)).1
      = σ_w.sload (accOut σ k (nestedSlot σ b ks)).1 :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w (fresh_nestedSlot_ne_cached hinv hc hmiss hpart)


end AttackVectors.NestedSlots
