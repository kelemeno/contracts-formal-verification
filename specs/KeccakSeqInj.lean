import specs.KeccakFuel
import specs.KeccakDistinct

/-
  SEQUENTIAL SLOT-INJECTIVITY — DERIVED FOR THE CASE THE CORPUS USES.

  `Clear.KeccakInjective.keccak256_inj` is the headline axiom: two successful calls with distinct preimages return
  distinct slots.  Its own header explains why it is stated without positing a global hash function — that would
  over-constrain the model's fresh-pick behaviour ACROSS DISJOINT STATE THREADS, where two independent fresh picks
  really could coincide.

  That caveat is what makes the axiom irreducible in general.  But it is NOT the situation the corpus reasons about:
  every use compares two calls made in ONE execution, the second running in the first's post-state.  And there the
  property is derivable, because the two branches are covered by facts already proved:

    * if the second call HITS, both slots are cached, and `CacheInj` turns equal slots into equal preimages;
    * if the second call MISSES, its slot is fresh while the first's is now cached, and `CacheInUsed` separates them.

  So the axiom's content, restricted to a single thread, needs no idealization at all.  Axiom-free.
-/

namespace Clear.KeccakSeqInj

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.KeccakFuel EVMState

/-- A step with fuel does not set the collision flag: the flag is only set when the pool is exhausted. -/
theorem clean_keccakOut {σ : EVMState} {p n : UInt256}
    (hfuel : Fuel σ 1) (hclean : σ.hash_collision = false) :
    (keccakOut σ p n).2.hash_collision = false := by
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some w => rw [keccakOut_of_cached hl]; exact hclean
  | none =>
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil =>
      exact absurd hpart (by
        have := Fuel.nonempty (n := 0) hfuel
        intro he; rw [he] at this; exact this rfl)
    | cons hd tl =>
      have hpost : (keccakOut σ p n).2
          = {σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p n) hd,
                    keccak_range := tl,
                    used_range := {hd} ∪ σ.used_range} := by
        unfold keccakOut EVMState.keccak256; simp only [hl, hpart]
      rw [hpost]
      exact hclean

/-- **SEQUENTIAL SLOT-INJECTIVITY.**  Two hash steps in one execution — the second running in the first's post-state
— return distinct slots when their preimages differ.

This is `keccak256_inj`'s content for the single-thread case, derived rather than assumed.  The two branches use the
two invariants: `CacheInj` when the second step hits, `CacheInUsed` (freshness) when it misses. -/
theorem keccakOut_seq_ne {σ : EVMState} {p₁ n₁ p₂ n₂ : UInt256}
    (hinv : CacheInUsed σ) (hinj : CacheInj σ)
    (hfuel : Fuel σ 2) (hclean : σ.hash_collision = false)
    (hne : mkInterval (keccakOut σ p₁ n₁).2.machine_state p₂ n₂
      ≠ mkInterval σ.machine_state p₁ n₁) :
    (keccakOut (keccakOut σ p₁ n₁).2 p₂ n₂).1 ≠ (keccakOut σ p₁ n₁).1 := by
  set σ₁ := (keccakOut σ p₁ n₁).2 with hσ₁
  set r₁ := (keccakOut σ p₁ n₁).1 with hr₁
  -- the first step's own result is cached in its post-state
  have hclean₁ : σ₁.hash_collision = false := clean_keccakOut (hfuel.mono (by omega)) hclean
  have hc₁ : Finmap.lookup (mkInterval σ.machine_state p₁ n₁) σ₁.keccak_map = some r₁ :=
    keccakOut_caches_of_clean hclean₁
  -- and both invariants survive it
  have hinv₁ : CacheInUsed σ₁ := cacheInUsed_keccakOut hinv
  have hinj₁ : CacheInj σ₁ := cacheInj_keccakOut hinv hinj
  have hfuel₁ : Fuel σ₁ 1 := Fuel.keccakOut (hfuel.mono (by omega))
  intro he
  cases hl : Finmap.lookup (mkInterval σ₁.machine_state p₂ n₂) σ₁.keccak_map with
  | some w =>
    -- a hit: both slots are cached, so injectivity forces the preimages equal
    have hval : (keccakOut σ₁ p₂ n₂).1 = w := by rw [keccakOut_of_cached hl]
    rw [hval] at he
    exact hne (hinj₁ _ _ r₁ (he ▸ hl) hc₁)
  | none =>
    -- a miss: the slot is fresh, while `r₁` is already cached
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ₁.used_range)) σ₁.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil =>
      exact absurd hpart (by
        have := Fuel.nonempty (n := 0) hfuel₁
        intro hq; rw [hq] at this; exact this rfl)
    | cons hd tl =>
      exact keccakOut_miss_fresh (σ := σ₁) hinv₁ hl hpart hc₁ he

/-! ## THE PAYOFF: NON-ALIASING WITHOUT THE AXIOM

`KeccakInjective.sload_sstore_keccak_of_preimage_ne` is the corpus's headline non-aliasing tool — a write at one
keccak slot preserves a read at another — and it is exactly where `keccak256_inj` enters. Both derived forms below
replace it.

The CACHED form is the one to reach for: every caller in this corpus already holds `Finmap.lookup … = some slot`
for both slots (that is how slots are named at all), so it costs nothing beyond `CacheInj`. The SEQUENTIAL form
covers the case where the second slot is computed fresh in the first's post-state. -/

/-- **NON-ALIASING FROM CACHED SLOTS.**  A write at one cached keccak slot preserves the read at another, when their
preimages differ.  Derived from `CacheInj` alone — no idealization. -/
theorem sload_sstore_of_cached_ne {σ σ_w : EVMState} {I₁ I₂ : List UInt256} {a b v : UInt256}
    (hinj : CacheInj σ)
    (hca : Finmap.lookup I₁ σ.keccak_map = some a)
    (hcb : Finmap.lookup I₂ σ.keccak_map = some b)
    (hne : I₁ ≠ I₂) :
    (σ_w.sstore b v).sload a = σ_w.sload a := by
  have hab : a ≠ b := fun he => hne (hinj I₁ I₂ a hca (he ▸ hcb))
  exact Clear.KeccakDistinct.sload_sstore_of_ne σ_w hab

/-- **NON-ALIASING FROM SEQUENTIAL CALLS.**  As above, for two slots computed in one execution — the second in the
first's post-state.  Derived from `keccakOut_seq_ne`. -/
theorem sload_sstore_of_seq_ne {σ σ_w : EVMState} {p₁ n₁ p₂ n₂ v : UInt256}
    (hinv : CacheInUsed σ) (hinj : CacheInj σ)
    (hfuel : Fuel σ 2) (hclean : σ.hash_collision = false)
    (hne : mkInterval (keccakOut σ p₁ n₁).2.machine_state p₂ n₂
      ≠ mkInterval σ.machine_state p₁ n₁) :
    (σ_w.sstore (keccakOut (keccakOut σ p₁ n₁).2 p₂ n₂).1 v).sload (keccakOut σ p₁ n₁).1
      = σ_w.sload (keccakOut σ p₁ n₁).1 :=
  Clear.KeccakDistinct.sload_sstore_of_ne σ_w
    (Ne.symm (keccakOut_seq_ne hinv hinj hfuel hclean hne))

end Clear.KeccakSeqInj
