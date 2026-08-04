import specs.KeccakDeterminism

/-
  R6 — THE `h`-INSTANTIATION.

  `MerkleSpec` and `specs/FoldWalkBridge.lean` are stated over an abstract node hash
  `h`, because Clear's keccak is FRESHNESS-based and has no global pure function: an
  uncached preimage draws a fresh slot, so `accOut` is genuinely state-dependent.
  `foldRoot_eq_rootOf` therefore carries

      hpure : ∀ σ' a b, (accOut σ' a b).1 = h a b

  which cannot hold for an arbitrary `h` and arbitrary states.  The blueprint's R6
  answer (§2, and §3 R6) is to read `h` OFF a reference state's keccak cache and rely
  on the walk having pre-cached every pair it uses.

  This file provides that reading and the agreement lemma.  `hashOf SF` is the
  cache-derived hash of a reference state `SF`; `accOut_eq_hashOf` says any state whose
  junk window matches `SF` and whose cache carries the same entry computes exactly it.

  Nothing here weakens the model: the cache hypothesis is precisely the obligation the
  concrete layer discharges by pre-caching (`walk_caches` in the IMT corpus), and
  without it the statement is FALSE, not merely unprovable.  Axiom-free.
-/

namespace Clear.CachedHash

open Clear Clear.KeccakDeterminism EVMState

/-- The node hash READ OFF a reference state's keccak cache.  `0` on a cache miss —
harmless, because every use is guarded by a hypothesis that the entry is present. -/
def hashOf (SF : EVMState) : UInt256 → UInt256 → UInt256 :=
  fun a b => (Finmap.lookup (accInterval SF a b) SF.keccak_map).getD 0

/-- On a cache hit, `hashOf` is the cached value. -/
theorem hashOf_eq_of_cached {SF : EVMState} {a b r : UInt256}
    (hc : Finmap.lookup (accInterval SF a b) SF.keccak_map = some r) :
    hashOf SF a b = r := by
  unfold hashOf
  rw [hc]
  rfl

/-- **R6.**  A state that agrees with the reference `SF` on the junk window and whose
cache carries `SF`'s entry for the pair computes exactly `hashOf SF` on it.

This is what discharges `FoldWalkBridge.foldRoot_eq_rootOf`'s `hpure` hypothesis, pair
by pair: the fold's hash behaves as the fixed function `hashOf SF` precisely on pairs
that have been pre-cached. -/
theorem accOut_eq_hashOf {SF σ : EVMState} {a b r : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i SF.machine_state.memory = Finmap.lookup i σ.machine_state.memory)
    (hcSF : Finmap.lookup (accInterval SF a b) SF.keccak_map = some r)
    (hcσ : Finmap.lookup (accInterval SF a b) σ.keccak_map = some r) :
    (accOut σ a b).1 = hashOf SF a b := by
  rw [hashOf_eq_of_cached hcSF]
  exact accOut_agree_value hframe hcσ

/-- The reference state computes its own cache-derived hash — the degenerate case, and
the one a caller instantiating `SF := σ` needs. -/
theorem accOut_eq_hashOf_self {SF : EVMState} {a b r : UInt256}
    (hc : Finmap.lookup (accInterval SF a b) SF.keccak_map = some r) :
    (accOut SF a b).1 = hashOf SF a b := by
  refine accOut_eq_hashOf (fun i _ _ => rfl) hc hc

end Clear.CachedHash
