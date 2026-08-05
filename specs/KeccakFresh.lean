import specs.KeccakDeterminism

/-
  FRESHNESS — WHY AN ATTACKER'S UNCACHED PAIR CANNOT MATCH A TREE NODE.

  `specs/MerkleProofSound.lean` proves that a walk reaching a tree's root must have used the tree's own
  siblings — but on `hinj`, pair-injectivity at ALL arguments.  Instantiating it with the deployed
  `CachedHash.hashOf SF` fails for a reason worth stating precisely: `hashOf` reads a cache, so an
  UNCACHED pair reads as `0`, and restricted injectivity says nothing about pairs the attacker chose.

  What actually rules the attacker out in this model is not collision resistance but FRESHNESS.
  `keccak256` on a cache miss draws its result from `keccak_range`'s unused portion and adds it to
  `used_range`; and every value ever cached was added to `used_range` when it was assigned.  So a
  freshly drawn hash differs from every value already in the cache — an attacker who supplies an
  unhashed preimage gets a slot that cannot coincide with any node the builder produced.

  This file proves that: the invariant, its preservation, and the consequence.  It is a statement about
  Clear's keccak MODEL rather than about keccak, which is exactly what makes it provable here instead
  of assumed — the four `Clear.KeccakInjective` idealizations are the assumed part.  Axiom-free.
-/

namespace Clear.KeccakFresh

open Clear Clear.KeccakDeterminism EVMState

/-- **THE INVARIANT.**  Every value in the keccak cache has been marked used. -/
def CacheInUsed (σ : EVMState) : Prop :=
  ∀ (I : List UInt256) (v : UInt256), Finmap.lookup I σ.keccak_map = some v → v ∈ σ.used_range

/-- A value drawn from the unused partition is not in `used_range`. -/
theorem partition_snd_not_used {σ : EVMState} {used unused : List UInt256} {r : UInt256}
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, unused))
    (hr : r ∈ unused) : r ∉ σ.used_range := by
  rw [List.partition_eq_filter_filter] at hpart
  have h2 : unused = σ.keccak_range.filter (fun x => !decide (x ∈ σ.used_range)) :=
    ((Prod.mk.injEq _ _ _ _).mp hpart).2.symm
  rw [h2, List.mem_filter] at hr
  have := hr.2
  simpa using this

/-- **PRESERVATION.**  `keccakOut` maintains the invariant: on a hit nothing changes, and on a miss the
new value is added to `used_range` in the same step that caches it. -/
theorem cacheInUsed_keccakOut {σ : EVMState} {p n : UInt256}
    (hinv : CacheInUsed σ) : CacheInUsed (keccakOut σ p n).2 := by
  unfold keccakOut EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some v => simpa [hl] using hinv
  | none =>
    cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
    | mk used unused =>
      cases unused with
      | nil =>
        simp only [hl, hpart]
        intro I v hv
        exact hinv I v hv
      | cons hd tl =>
        simp only [hl, hpart]
        intro I v hv
        by_cases hI : I = mkInterval σ.machine_state p n
        · subst hI
          rw [Finmap.lookup_insert] at hv
          have : v = hd := (Option.some.inj hv).symm
          subst this
          exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
        · rw [Finmap.lookup_insert_of_ne _ hI] at hv
          exact Finset.mem_union_right _ (hinv I v hv)

/-- **FRESH ≠ CACHED.**  On a cache miss the returned hash differs from every value already cached —
so a preimage the state has not hashed cannot produce a hash it has.

This is the fact that rules out an attacker's unhashed path matching a builder's node, and it is
freshness, not collision resistance: no assumption about keccak is used. -/
theorem keccakOut_miss_ne_cached {σ : EVMState} {p n : UInt256}
    (hinv : CacheInUsed σ)
    (hmiss : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = none)
    {I : List UInt256} {v : UInt256}
    (hcached : Finmap.lookup I σ.keccak_map = some v) :
    (keccakOut σ p n).1 ≠ v ∨ (keccakOut σ p n).1 = 0 := by
  unfold keccakOut EVMState.keccak256
  cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
  | mk used unused =>
    cases unused with
    | nil =>
      -- the range is exhausted: the model returns the collision sentinel
      right; simp [hmiss, hpart]
    | cons hd tl =>
      left
      simp only [hmiss, hpart]
      intro he
      have hused : v ∈ σ.used_range := hinv I v hcached
      have hfresh : hd ∉ σ.used_range :=
        partition_snd_not_used hpart (List.mem_cons_self _ _)
      exact hfresh (he ▸ hused)

/-- The clean form: when the range has not been exhausted, a miss's value is genuinely new. -/
theorem keccakOut_miss_fresh {σ : EVMState} {p n : UInt256} {used : List UInt256}
    {hd : UInt256} {tl : List UInt256}
    (hinv : CacheInUsed σ)
    (hmiss : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = none)
    (hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range = (used, hd :: tl))
    {I : List UInt256} {v : UInt256}
    (hcached : Finmap.lookup I σ.keccak_map = some v) :
    (keccakOut σ p n).1 ≠ v := by
  unfold keccakOut EVMState.keccak256
  simp only [hmiss, hpart]
  intro he
  exact (partition_snd_not_used hpart (List.mem_cons_self _ _)) (he ▸ hinv I v hcached)

/-- `mstore` preserves the invariant — it touches neither the cache nor `used_range`. -/
theorem cacheInUsed_mstore {σ : EVMState} (a v : UInt256) (hinv : CacheInUsed σ) :
    CacheInUsed (σ.mstore a v) := hinv

/-- Hence `accOut` preserves it: two scratch writes and a keccak step. -/
theorem cacheInUsed_accOut {σ : EVMState} {key base : UInt256}
    (hinv : CacheInUsed σ) : CacheInUsed (accOut σ key base).2 :=
  cacheInUsed_keccakOut (cacheInUsed_mstore 32 base (cacheInUsed_mstore 0 key hinv))

/-! ## CACHE INJECTIVITY IS PRESERVED

The descent needs cache injectivity at the state where it applies the forgery atom — i.e. at every depth of
a fold.  Requiring it as a hypothesis at each depth would be ugly, and it turns out to be unnecessary:
hashing cannot BREAK injectivity, because the value a miss assigns is fresh, so it cannot collide with a
value already cached.

So injectivity, like the invariant itself, needs stating only at the start. -/

/-- Keccak is injective on the preimages this state has hashed. -/
def CacheInj (σ : EVMState) : Prop :=
  ∀ (I J : List UInt256) (r : UInt256),
    Finmap.lookup I σ.keccak_map = some r → Finmap.lookup J σ.keccak_map = some r → I = J

/-- **PRESERVATION.**  A hash step cannot break cache injectivity: on a hit nothing changes, and on a miss
the new value is fresh, so it cannot equal any value already cached — the only way a new entry could have
violated injectivity. -/
theorem cacheInj_keccakOut {σ : EVMState} {p n : UInt256}
    (hinv : CacheInUsed σ) (hinj : CacheInj σ) : CacheInj (keccakOut σ p n).2 := by
  unfold keccakOut EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some v => simpa [hl] using hinj
  | none =>
    cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
    | mk used unused =>
      cases unused with
      | nil => simp only [hl, hpart]; exact hinj
      | cons hd tl =>
        simp only [hl, hpart]
        have hfresh : hd ∉ σ.used_range :=
          partition_snd_not_used hpart (List.mem_cons_self _ _)
        intro I J r hI hJ
        by_cases hIe : I = mkInterval σ.machine_state p n
        · by_cases hJe : J = mkInterval σ.machine_state p n
          · rw [hIe, hJe]
          · -- `J` is an old entry, so `r` was already cached and hence used; but `r = hd` is fresh
            exfalso
            rw [hIe, Finmap.lookup_insert] at hI
            rw [Finmap.lookup_insert_of_ne _ hJe] at hJ
            exact hfresh ((Option.some.inj hI) ▸ hinv J r hJ)
        · by_cases hJe : J = mkInterval σ.machine_state p n
          · exfalso
            rw [hJe, Finmap.lookup_insert] at hJ
            rw [Finmap.lookup_insert_of_ne _ hIe] at hI
            exact hfresh ((Option.some.inj hJ) ▸ hinv I r hI)
          · rw [Finmap.lookup_insert_of_ne _ hIe] at hI
            rw [Finmap.lookup_insert_of_ne _ hJe] at hJ
            exact hinj I J r hI hJ

/-- `mstore` preserves injectivity — it does not touch the cache. -/
theorem cacheInj_mstore {σ : EVMState} (a v : UInt256) (hinj : CacheInj σ) :
    CacheInj (σ.mstore a v) := hinj

/-- Hence an accessor step preserves it. -/
theorem cacheInj_accOut {σ : EVMState} {key base : UInt256}
    (hinv : CacheInUsed σ) (hinj : CacheInj σ) : CacheInj (accOut σ key base).2 :=
  cacheInj_keccakOut (cacheInUsed_mstore 32 base (cacheInUsed_mstore 0 key hinv))
    (cacheInj_mstore 32 base (cacheInj_mstore 0 key hinj))

end Clear.KeccakFresh
