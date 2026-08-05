import specs.KeccakFuel

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

end Clear.KeccakSeqInj
