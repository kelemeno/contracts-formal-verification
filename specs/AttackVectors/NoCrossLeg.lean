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

/-! ## THE UNSEEN LEG

`NoCrossBundle.fresh_slot_ne_cached` was stated over an ARBITRARY base rather than a fixed one, and
that pays off here: the nested case's outer accessor has an intermediate as its base, so the unseen-leg
result is that lemma instantiated, not a new argument.  The mechanism is again freshness — the slot is
drawn from the unused pool, and every cached slot has been marked used. -/

/-- **A NEVER-COMPUTED LEG'S SLOT IS FRESH.**  If the second leg's OUTER accessor preimage is not
cached, its slot differs from the first leg's — whatever the intermediates were. -/
theorem fresh_leg_slot_ne_cached {σ : EVMState} (hinv : CacheInUsed σ)
    {b₂ i₂ r₁ : UInt256} {I₁ : List UInt256}
    {used : List UInt256} {hd : UInt256} {tl : List UInt256}
    (hc₁ : Finmap.lookup I₁ σ.keccak_map = some r₁)
    (hmiss : Finmap.lookup (accInterval σ b₂ i₂) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl)) :
    (accOut σ b₂ i₂).1 ≠ r₁ :=
  Clear.KeccakFresh.keccakOut_miss_fresh
    (σ := (σ.mstore 0 b₂).mstore 32 i₂)
    (Clear.KeccakFresh.cacheInUsed_mstore 32 i₂
      (Clear.KeccakFresh.cacheInUsed_mstore 0 b₂ hinv))
    hmiss hpart hc₁

/-- **NO INTERFERENCE WITH AN UNSEEN LEG.**  A refund write at one leg's slot is invisible at the slot
an unseen leg draws, so its state byte reads whatever it read before. -/
theorem legState_frames_fresh_leg {σ σ_w : EVMState} (hinv : CacheInUsed σ)
    {b₂ i₂ r₁ v : UInt256} {I₁ : List UInt256}
    {used : List UInt256} {hd : UInt256} {tl : List UInt256}
    (hc₁ : Finmap.lookup I₁ σ.keccak_map = some r₁)
    (hmiss : Finmap.lookup (accInterval σ b₂ i₂) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl)) :
    AtomicFlowManager.Layout.legStateOf (σ_w.sstore r₁ v) (accOut σ b₂ i₂).1
      = AtomicFlowManager.Layout.legStateOf σ_w (accOut σ b₂ i₂).1 := by
  unfold AtomicFlowManager.Layout.legStateOf
  rw [Clear.KeccakDistinct.sload_sstore_of_ne σ_w
    (fresh_leg_slot_ne_cached hinv hc₁ hmiss hpart)]

/-! ## THE LOOP FORM

A multi-leg flow refunds several legs in sequence, so the frame a real run needs is not "one other
leg's write is harmless" but "the whole loop leaves this leg alone".  Folding the pairwise frame over
a list of writes gives that.

The hypothesis is per-write and local: each write in the list is at a leg differing from ours in one
coordinate, with its accessor steps hashed.  Nothing is assumed about the ORDER of the writes or about
how many there are. -/

/-- **A LEG'S STATE SURVIVES A WHOLE REFUND LOOP.**  Given a list of writes, each at some other leg's
slot, the leg at `(f, b)` reads exactly what it read before the loop ran.

Each entry carries its own `(flowId, bundleHash, intermediate, slot, value)` and the evidence that its
accessor steps were hashed, so this composes directly with a loop that refunds legs one at a time. -/
theorem legState_survives_refund_loop {σ : EVMState} (hinj : CacheInj σ)
    {f b base i r : UInt256}
    (hi : Finmap.lookup (accInterval σ f base) σ.keccak_map = some i)
    (ho : Finmap.lookup (accInterval σ b i) σ.keccak_map = some r) :
    ∀ (ws : List (UInt256 × UInt256 × UInt256 × UInt256 × UInt256)) (σ_w : EVMState),
      (∀ p ∈ ws,
        (p.1 ≠ f ∨ p.2.1 ≠ b) ∧
        Finmap.lookup (accInterval σ p.1 base) σ.keccak_map = some p.2.2.1 ∧
        Finmap.lookup (accInterval σ p.2.1 p.2.2.1) σ.keccak_map = some p.2.2.2.1) →
      AtomicFlowManager.Layout.legStateOf
          (ws.foldl (fun s p => s.sstore p.2.2.2.1 p.2.2.2.2) σ_w) r
        = AtomicFlowManager.Layout.legStateOf σ_w r := by
  intro ws
  induction ws with
  | nil => intro σ_w _; rfl
  | cons p rest ih =>
    intro σ_w hall
    obtain ⟨hne, hip, hop⟩ := hall p (List.mem_cons_self _ _)
    rw [List.foldl_cons, ih _ (fun q hq => hall q (List.mem_cons_of_mem _ hq))]
    exact legState_frames_other_leg hinj hip hi hop ho hne

end AttackVectors.NoCrossLeg
