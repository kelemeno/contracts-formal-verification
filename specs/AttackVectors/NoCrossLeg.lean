import specs.AttackVectors.NoCrossBundle
import specs.AtomicFlowManager.Layout

/-
  NO CROSS-LEG INTERFERENCE — the two-level mapping case.

  `AtomicFlowManager.Layout`'s refund results — `refunded_leg_cannot_refund_again` and
  `refund_write_sets_reverted` — are both about ONE slot.  As with the bundle status
  (`AttackVectors.NoCrossBundle`), that leaves the cross-leg question open: nothing there rules out
  the refund write for one leg disturbing another leg's state byte, which would either forge a
  `Reverted` (blocking a legitimate refund) or clear one (enabling a second payout — a direct theft,
  since `claimRefund` is where funds actually move).

  Legs live in `_state[flowId][bundleHash]`, a TWO-LEVEL mapping, so the slot is a nested accessor:
  the inner step hashes `(flowId, base)` to an intermediate, the outer hashes `(bundleHash, inner)`.
  Two legs differ if EITHER coordinate differs, and the two cases separate differently:

    * different `bundleHash`, same flow — the outer accessors differ in their KEY;
    * different `flowId` — the inner slots differ, so the outer accessors differ in their BASE.

  `CachedHashInj.accInterval_inj` gives both components of the preimage at once, which is what lets a
  single argument cover both.  Axiom-free.
-/

namespace AttackVectors.NoCrossLeg

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.CachedHashInj

/-- **NESTED ACCESSOR SEPARATION.**  Two legs whose `(flowId, bundleHash)` pairs differ in EITHER
coordinate land on different storage slots, provided every accessor step involved has been hashed.

The proof takes the outer step first: equal slots force equal outer preimages, hence equal
`bundleHash` AND equal intermediates; the intermediates then force equal `flowId`.  So a difference
in either coordinate propagates out. -/
theorem leg_slot_ne {σ : EVMState} (hinj : CacheInj σ)
    {f₁ f₂ b₁ b₂ base i₁ i₂ r₁ r₂ : UInt256}
    (hi₁ : Finmap.lookup (accInterval σ f₁ base) σ.keccak_map = some i₁)
    (hi₂ : Finmap.lookup (accInterval σ f₂ base) σ.keccak_map = some i₂)
    (ho₁ : Finmap.lookup (accInterval σ b₁ i₁) σ.keccak_map = some r₁)
    (ho₂ : Finmap.lookup (accInterval σ b₂ i₂) σ.keccak_map = some r₂)
    (hne : f₁ ≠ f₂ ∨ b₁ ≠ b₂) : r₁ ≠ r₂ := by
  intro he
  -- equal slots ⇒ equal outer preimages ⇒ equal bundleHash and equal intermediate
  obtain ⟨hb, hint⟩ := accInterval_inj (hinj _ _ r₁ ho₁ (he ▸ ho₂))
  rcases hne with hf | hb' 
  · -- different flow: the intermediates coincide, so the inner preimages do, so the flows do
    exact hf (accInterval_inj (hinj _ _ i₁ hi₁ (hint ▸ hi₂))).1
  · exact hb' hb

/-- **NO CROSS-LEG INTERFERENCE.**  The refund write for one leg leaves a different leg's state slot
exactly as it was — whether the legs differ by flow or by bundle.

So `refunded_leg_cannot_refund_again` cannot be defeated sideways: the write that records one leg's
refund is invisible at every other leg's slot, and in particular cannot clear a `Reverted` byte to
enable a second payout. -/
theorem refund_write_frames_other_leg {σ σ_w : EVMState} (hinj : CacheInj σ)
    {f₁ f₂ b₁ b₂ base i₁ i₂ r₁ r₂ v : UInt256}
    (hi₁ : Finmap.lookup (accInterval σ f₁ base) σ.keccak_map = some i₁)
    (hi₂ : Finmap.lookup (accInterval σ f₂ base) σ.keccak_map = some i₂)
    (ho₁ : Finmap.lookup (accInterval σ b₁ i₁) σ.keccak_map = some r₁)
    (ho₂ : Finmap.lookup (accInterval σ b₂ i₂) σ.keccak_map = some r₂)
    (hne : f₁ ≠ f₂ ∨ b₁ ≠ b₂) :
    (σ_w.sstore r₁ v).sload r₂ = σ_w.sload r₂ :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w (Ne.symm (leg_slot_ne hinj hi₁ hi₂ ho₁ ho₂ hne))

/-- **THE LEG'S STATE BYTE IS UNTOUCHED.**  The frame at the level the guard actually reads:
`legStateOf` of the other leg is unchanged, so its `Revertable` / `Reverted` classification — and
hence whether `claimRefund` pays out — cannot be moved by another leg's write. -/
theorem legState_frames_other_leg {σ σ_w : EVMState} (hinj : CacheInj σ)
    {f₁ f₂ b₁ b₂ base i₁ i₂ r₁ r₂ v : UInt256}
    (hi₁ : Finmap.lookup (accInterval σ f₁ base) σ.keccak_map = some i₁)
    (hi₂ : Finmap.lookup (accInterval σ f₂ base) σ.keccak_map = some i₂)
    (ho₁ : Finmap.lookup (accInterval σ b₁ i₁) σ.keccak_map = some r₁)
    (ho₂ : Finmap.lookup (accInterval σ b₂ i₂) σ.keccak_map = some r₂)
    (hne : f₁ ≠ f₂ ∨ b₁ ≠ b₂) :
    AtomicFlowManager.Layout.legStateOf (σ_w.sstore r₁ v) r₂
      = AtomicFlowManager.Layout.legStateOf σ_w r₂ := by
  unfold AtomicFlowManager.Layout.legStateOf
  rw [refund_write_frames_other_leg hinj hi₁ hi₂ ho₁ ho₂ hne]

end AttackVectors.NoCrossLeg
