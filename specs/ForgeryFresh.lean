import specs.KeccakFresh
import specs.CachedHashInj

/-
  CONCRETE FORGERY RESISTANCE: A STEP PRODUCING A BUILDER'S VALUE USED THE BUILDER'S PAIR.

  `specs/MerkleProofSound.lean` gives proof soundness on pair-injectivity at all arguments, which the
  deployed cache-derived hash does not have.  `specs/KeccakFresh.lean` supplies what does the work
  instead.  This file combines the two ingredients into the atom the concrete argument needs.

  The reasoning, at one hash step:

    * the attacker's step must be a cache HIT.  If it missed, its value would be freshly drawn and so
      distinct from every already-cached value — but the value it has to produce (a node the builder
      computed) IS cached.  Freshness, not collision resistance.
    * a hit means the attacker's own preimage is in the cache mapped to that value.  Cache injectivity
      then forces it to BE the builder's preimage, and `CachedHashInj.accInterval_inj` reads the pair
      back off the preimage.

  So at every step where an attacker must reproduce a builder-computed value, it is forced to use the
  builder's exact arguments.  Applied top-down along a path this is what makes a forged Merkle proof
  impossible in the concrete model — the descent itself is the remaining assembly, and the two facts it
  needs are here.  Axiom-free.
-/

namespace Clear.ForgeryFresh

open Clear Clear.KeccakDeterminism Clear.KeccakFresh Clear.CachedHashInj EVMState

/-- The keccak bookkeeping fields are untouched by the accessor's scratch writes. -/
private lemma acc_state_fields (σ : EVMState) (a b : UInt256) :
    ((σ.mstore 0 a).mstore 32 b).keccak_map = σ.keccak_map
    ∧ ((σ.mstore 0 a).mstore 32 b).used_range = σ.used_range
    ∧ ((σ.mstore 0 a).mstore 32 b).keccak_range = σ.keccak_range :=
  ⟨rfl, rfl, rfl⟩

/-- **A STEP PRODUCING A CACHED VALUE WAS A HIT.**  If an accessor step outputs a value that is already
in the cache, then the step's own preimage was in the cache mapped to that value.

This is freshness doing the work: a miss would return a value drawn from the unused range, which by
`CacheInUsed` cannot equal anything already cached. -/
theorem accOut_hit_of_output_cached {σ : EVMState} {a b v : UInt256} {I : List UInt256}
    (hinv : CacheInUsed σ)
    (hfuel : (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ [])
    (hI : Finmap.lookup I σ.keccak_map = some v)
    (hout : (accOut σ a b).1 = v) :
    Finmap.lookup (accInterval σ a b) σ.keccak_map = some v := by
  obtain ⟨hmap, hused, hrange⟩ := acc_state_fields σ a b
  set σ' := (σ.mstore 0 a).mstore 32 b with hσ'
  cases hl : Finmap.lookup (accInterval σ a b) σ.keccak_map with
  | some r =>
    -- a hit: the step returned `r`, and `r = v`
    have hstep : (accOut σ a b).1 = r := by
      unfold accOut
      rw [keccakOut_of_cached (σ := σ') (p := 0) (n := 64) (r := r) (by rw [hmap]; exact hl)]
    rw [hstep] at hout
    exact congrArg some hout
  | none =>
    -- a miss: the value is fresh, contradicting that `v` is cached
    exfalso
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    cases unused with
    | nil => rw [hpart] at hfuel; exact hfuel rfl
    | cons hd tl =>
      have hmiss : Finmap.lookup (mkInterval σ'.machine_state 0 64) σ'.keccak_map = none := by
        rw [hmap]; exact hl
      have hne : (keccakOut σ' 0 64).1 ≠ v :=
        keccakOut_miss_fresh (σ := σ') (by rw [hσ']; exact hinv) hmiss
          (by rw [hused, hrange]; exact hpart) (by rw [hmap]; exact hI)
      exact hne hout

/-- **THE ATTACKER IS FORCED ONTO THE BUILDER'S ARGUMENTS.**  If an accessor step outputs a value the
builder produced from `(c, d)`, then the step's own arguments ARE `(c, d)`.

Both ingredients appear explicitly: freshness forces the step to hit, and cache injectivity plus the
accessor layout fact read the arguments off the preimage.  The only cryptographic hypothesis is
`hcinj` — the same one the rest of the chain uses. -/
theorem accOut_args_forced {σ : EVMState} {a b c d v : UInt256}
    (hinv : CacheInUsed σ)
    (hfuel : (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ [])
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I σ.keccak_map = some r →
        Finmap.lookup J σ.keccak_map = some r → I = J)
    (hbuilder : Finmap.lookup (accInterval σ c d) σ.keccak_map = some v)
    (hout : (accOut σ a b).1 = v) :
    a = c ∧ b = d := by
  have hhit : Finmap.lookup (accInterval σ a b) σ.keccak_map = some v :=
    accOut_hit_of_output_cached hinv hfuel hbuilder hout
  exact accInterval_inj (hcinj _ _ v hhit hbuilder)

/-- **NON-INCLUSION FORM.**  An accessor step on arguments that differ from the builder's cannot
reproduce the builder's value — for arbitrary attacker-chosen arguments, with no assumption that they
were ever hashed. -/
theorem accOut_ne_of_args_ne {σ : EVMState} {a b c d v : UInt256}
    (hinv : CacheInUsed σ)
    (hfuel : (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ [])
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I σ.keccak_map = some r →
        Finmap.lookup J σ.keccak_map = some r → I = J)
    (hbuilder : Finmap.lookup (accInterval σ c d) σ.keccak_map = some v)
    (hne : ¬(a = c ∧ b = d)) :
    (accOut σ a b).1 ≠ v :=
  fun hout => hne (accOut_args_forced hinv hfuel hcinj hbuilder hout)

end Clear.ForgeryFresh
