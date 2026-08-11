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

end AttackVectors.NestedSlots
