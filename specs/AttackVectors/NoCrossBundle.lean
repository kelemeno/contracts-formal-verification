import specs.KeccakSeqInj
import specs.CachedHashInj

/-
  NO CROSS-BUNDLE INTERFERENCE — axiom-free.

  `InteropHandler.delivered_status_reads_two` proves no double delivery at the LEG level: after
  `_markFullyExecutedAndRun`'s status write, re-reading the slot returns `2 = FullyExecuted`, so a
  second delivery of the same bundle is rejected by its own first write.

  But it is stated at a GENERIC slot `d`.  Nothing there ties `d` to a particular bundle, so it says
  nothing about a DIFFERENT bundle: for all that theorem knows, marking bundle A delivered could
  overwrite bundle B's status and either forge a delivery or erase one.  The status slot is
  `accOut evm bundleHash 1` (that file's "Block 1 closed form"), so ruling this out is a
  slot-separation question about two mapping keys.

  That is what this file proves, and it needs no idealization: `CachedHashInj.accInterval_inj` says
  the accessor preimage determines both the key and the base, and `KeccakFresh.CacheInj` turns
  distinct preimages into distinct slots.  Both are derived — see `keccak-trusted-base-derived`.

  WHAT THIS DOES NOT SAY.  Both bundles' status slots must already be CACHED in the reference state,
  which is what a run that has touched both bundles gives.  Nothing here covers a bundle whose slot
  has never been computed: its slot is drawn fresh, and freshness — not this argument — is what
  separates it (`KeccakFresh.keccakOut_miss_fresh`).  Axiom-free.
-/

namespace AttackVectors.NoCrossBundle

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakSeqInj Clear.CachedHashInj

/-- **DISTINCT KEYS GIVE DISTINCT SLOTS.**  Two mapping accessors over the same base whose keys
differ, both already hashed, land on different storage slots. -/
theorem status_slot_ne_of_key_ne {σ : EVMState} (hinj : CacheInj σ)
    {k₁ k₂ base r₁ r₂ : UInt256}
    (hc₁ : Finmap.lookup (accInterval σ k₁ base) σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup (accInterval σ k₂ base) σ.keccak_map = some r₂)
    (hk : k₁ ≠ k₂) : r₁ ≠ r₂ := by
  intro he
  exact hk (accInterval_inj (hinj _ _ r₁ hc₁ (he ▸ hc₂))).1

/-- **NO CROSS-BUNDLE INTERFERENCE.**  Marking one bundle's status leaves a different bundle's status
exactly as it was.

So `delivered_status_reads_two`'s leg-level no-double-delivery cannot be defeated by marking a
different bundle: the write that records delivery of `k₁` is invisible at `k₂`'s slot. -/
theorem status_write_frames_other_bundle {σ σ_w : EVMState} (hinj : CacheInj σ)
    {k₁ k₂ base r₁ r₂ v : UInt256}
    (hc₁ : Finmap.lookup (accInterval σ k₁ base) σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup (accInterval σ k₂ base) σ.keccak_map = some r₂)
    (hk : k₁ ≠ k₂) :
    (σ_w.sstore r₁ v).sload r₂ = σ_w.sload r₂ :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w
    (Ne.symm (status_slot_ne_of_key_ne hinj hc₁ hc₂ hk))

/-- **NEITHER DIRECTION.**  The frame holds both ways round, so marking `k₂` equally cannot disturb
`k₁` — a delivery cannot be ERASED by another bundle's write any more than it can be forged. -/
theorem status_write_frames_symm {σ σ_w : EVMState} (hinj : CacheInj σ)
    {k₁ k₂ base r₁ r₂ v : UInt256}
    (hc₁ : Finmap.lookup (accInterval σ k₁ base) σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup (accInterval σ k₂ base) σ.keccak_map = some r₂)
    (hk : k₁ ≠ k₂) :
    (σ_w.sstore r₂ v).sload r₁ = σ_w.sload r₁ :=
  status_write_frames_other_bundle hinj hc₂ hc₁ (Ne.symm hk)

/-- **THE STATUS SURVIVES ANY NUMBER OF OTHER BUNDLES' WRITES.**  Folding the frame over a list of
writes at other bundles' slots: a bundle's recorded status is untouched by all of them.

This is the form the delivery argument wants — not "one other write is harmless" but "no sequence of
other bundles' markings can move it". -/
theorem status_survives_other_writes {σ : EVMState} (hinj : CacheInj σ)
    {base k : UInt256} {r : UInt256}
    (hc : Finmap.lookup (accInterval σ k base) σ.keccak_map = some r) :
    ∀ (ws : List (UInt256 × UInt256 × UInt256)) (σ_w : EVMState),
      (∀ p ∈ ws, p.1 ≠ k ∧
        Finmap.lookup (accInterval σ p.1 base) σ.keccak_map = some p.2.1) →
      (ws.foldl (fun s p => s.sstore p.2.1 p.2.2) σ_w).sload r = σ_w.sload r := by
  intro ws
  induction ws with
  | nil => intro σ_w _; rfl
  | cons p rest ih =>
    intro σ_w hall
    obtain ⟨hne, hcp⟩ := hall p (List.mem_cons_self _ _)
    rw [List.foldl_cons, ih _ (fun q hq => hall q (List.mem_cons_of_mem _ hq))]
    exact status_write_frames_other_bundle hinj hcp hc hne

/-! ## THE OTHER HALF: A BUNDLE WHOSE SLOT WAS NEVER COMPUTED

The results above need both slots CACHED, so they cover bundles a run has already touched.  The
remaining case is a bundle whose status slot has never been computed — and there the separating
argument is not injectivity at all but FRESHNESS: the slot is drawn from the unused pool, and
`KeccakFresh.CacheInUsed` says every cached value has been marked used, so the fresh draw differs
from all of them.

Stating it completes the picture: whether or not the second bundle has been seen before, a write at
the first bundle's slot is invisible at the second's. -/

/-- **A NEVER-COMPUTED BUNDLE'S SLOT IS FRESH.**  If the second bundle's accessor preimage is not in
the cache, computing it yields a slot distinct from any cached slot — in particular from the first
bundle's.

The non-exhaustion hypothesis is necessary and not bookkeeping: an exhausted pool makes the model
return `0` and flag a collision, and `0` could well be a cached slot. -/
theorem fresh_slot_ne_cached {σ : EVMState} (hinv : CacheInUsed σ)
    {k₁ k₂ base r₁ : UInt256} {used : List UInt256} {hd : UInt256} {tl : List UInt256}
    (hc₁ : Finmap.lookup (accInterval σ k₁ base) σ.keccak_map = some r₁)
    (hmiss : Finmap.lookup (accInterval σ k₂ base) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl)) :
    (accOut σ k₂ base).1 ≠ r₁ := by
  refine Clear.KeccakFresh.keccakOut_miss_fresh
    (σ := (σ.mstore 0 k₂).mstore 32 base)
    (Clear.KeccakFresh.cacheInUsed_mstore 32 base
      (Clear.KeccakFresh.cacheInUsed_mstore 0 k₂ hinv))
    hmiss hpart hc₁

/-- **NO INTERFERENCE WITH AN UNSEEN BUNDLE.**  A write at one bundle's status slot is invisible at
the slot a never-computed bundle draws.

With `status_write_frames_other_bundle` this covers both cases, so no bundle's status — recorded or
not yet computed — can be moved by another bundle's marking. -/
theorem status_write_frames_fresh_bundle {σ σ_w : EVMState} (hinv : CacheInUsed σ)
    {k₁ k₂ base r₁ v : UInt256} {used : List UInt256} {hd : UInt256} {tl : List UInt256}
    (hc₁ : Finmap.lookup (accInterval σ k₁ base) σ.keccak_map = some r₁)
    (hmiss : Finmap.lookup (accInterval σ k₂ base) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl)) :
    (σ_w.sstore r₁ v).sload (accOut σ k₂ base).1 = σ_w.sload (accOut σ k₂ base).1 :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w (fresh_slot_ne_cached hinv hc₁ hmiss hpart)

end AttackVectors.NoCrossBundle
