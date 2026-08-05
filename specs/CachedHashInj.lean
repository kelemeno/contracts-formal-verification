import specs.CachedHash
import specs.LeafHashWindow

/-
  THE TWO CRYPTOGRAPHIC HYPOTHESES REDUCE TO ONE.

  The chain now carries two named cryptographic assumptions:

    * node-hash pair-injectivity   (`hnodeinj`, used by MerkleSpec's M-D family)
    * leaf-hash injectivity        (`hinj`, discharged for the deployed hash in
                                   `LeafDecode3.lh3_inj_on_cached`)

  `LeafHashWindow.leafInterval_inj` showed the second is not an independent assumption: the
  keccak PREIMAGE of `fun_hashLeaf` determines all three leaf fields, so leaf-hash injectivity
  follows from injectivity of the keccak cache on preimages.

  The node hash admits exactly the same treatment, and this file gives it.  The accessor
  preimage `accInterval σ a b` is the 64-byte scratch holding `a` at word 0 and `b` at word 32,
  so it determines `(a, b)` — hence node-hash pair-injectivity also reduces to cache
  injectivity.

  So both cryptographic hypotheses in the corpus are the SAME hypothesis: keccak is injective on
  the preimages it has actually hashed.  That is the model-level form of collision resistance,
  and it is the only cryptographic idealization the fold / root-binding track needs.

  WHAT THIS DOES NOT DO.  It does not restrict `MerkleSpec`'s M-D family to cached pairs.
  `rootOf_inj_of_h_inj` asks for pair-injectivity of `h` at ALL arguments, and a cache-derived
  hash cannot have that — the same over-strength that forced four weakenings in
  `FoldWalkBridge` and the restricted form of `root_binding`.  Restricting M-D means threading a
  "cached" predicate through the level-by-level induction over `rootOf`, which is real work, not
  a rephrasing.  The atoms below are what that work would consume.  Axiom-free.
-/

namespace Clear.CachedHashInj

open Clear Clear.KeccakDeterminism Clear.CachedHash Clear.LeafHashWindow EVMState

set_option maxHeartbeats 400000

/-- The accessor scratch reads back `a` at word 0. -/
theorem accWrites_read_fst (σ : EVMState) (a b : UInt256) :
    ((σ.mstore 0 a).mstore 32 b).machine_state.lookupMemory 0 = a := by
  have h0 : ((0 : UInt256)).val = 0 := by decide
  have h32 : ((32 : UInt256)).val = 32 := by decide
  have hms : ((σ.mstore 0 a).mstore 32 b).machine_state
      = (σ.machine_state.updateMemory 0 a).updateMemory 32 b := rfl
  rw [hms]
  rw [lookupMemory_updateMemory_outside _ 32 b 0 (by rw [h32]; norm_num)
      (by rw [h0]; norm_num) (by left; rw [h0, h32])]
  exact lookupMemory_updateMemory_self' _ 0 a (by rw [h0]; norm_num)

/-- The accessor scratch reads back `b` at word 32. -/
theorem accWrites_read_snd (σ : EVMState) (a b : UInt256) :
    ((σ.mstore 0 a).mstore 32 b).machine_state.lookupMemory 32 = b := by
  have h32 : ((32 : UInt256)).val = 32 := by decide
  have hms : ((σ.mstore 0 a).mstore 32 b).machine_state
      = (σ.machine_state.updateMemory 0 a).updateMemory 32 b := rfl
  rw [hms]
  exact lookupMemory_updateMemory_self' _ 32 b (by rw [h32]; norm_num)

/-- **THE ACCESSOR LAYOUT FACT.**  The keccak preimage of one accessor step determines both of
its arguments.  As with `leafInterval_inj`, the two states are arbitrary and unrelated: the
arguments are recovered from the written scratch alone. -/
theorem accInterval_inj {σ₁ σ₂ : EVMState} {a b c d : UInt256}
    (h : accInterval σ₁ a b = accInterval σ₂ c d) : a = c ∧ b = d := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h0 : ((0 : UInt256)).val = 0 := by decide
  have h64 : ((64 : UInt256)).val = 64 := by decide
  have key : ∀ {σ x y : _} (j : ℕ) (addr : UInt256), j < 64 →
      (0 : UInt256) + (j : UInt256) = addr →
      ((σ.mstore 0 x).mstore 32 y).machine_state.lookupMemory addr
        = ((accInterval σ x y).get? j).get! := by
    intro σ x y j addr hj haddr
    unfold accInterval
    rw [mkInterval_get? (by rw [h64]; exact hj), haddr]
    rfl
  have e0 : (0 : UInt256) + ((0 : ℕ) : UInt256) = 0 := by
    have : (((0 : ℕ)) : UInt256) = 0 := by decide
    rw [this, add_zero]
  have e32 : (0 : UInt256) + ((32 : ℕ) : UInt256) = 32 := by
    have : (((32 : ℕ)) : UInt256) = (32 : UInt256) := by decide
    rw [this, zero_add]
  refine ⟨?_, ?_⟩
  · rw [← accWrites_read_fst σ₁ a b, ← accWrites_read_fst σ₂ c d,
        key 0 0 (by norm_num) e0, key 0 0 (by norm_num) e0, h]
  · rw [← accWrites_read_snd σ₁ a b, ← accWrites_read_snd σ₂ c d,
        key 32 32 (by norm_num) e32, key 32 32 (by norm_num) e32, h]

/-- **NODE-HASH PAIR-INJECTIVITY, DERIVED.**  On cached pairs, the accessor hash is
pair-injective — from keccak cache injectivity alone.

Together with `LeafDecode3.lh3_inj_on_cached` this collapses the corpus's two cryptographic
hypotheses into one: keccak is injective on the preimages it has hashed. -/
theorem hashOf_pair_inj {SF : EVMState}
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    {a b c d r : UInt256}
    (h₁ : Finmap.lookup (accInterval SF a b) SF.keccak_map = some r)
    (h₂ : Finmap.lookup (accInterval SF c d) SF.keccak_map = some r) :
    a = c ∧ b = d :=
  accInterval_inj (hcinj _ _ r h₁ h₂)

/-- Value form: two cached pairs with equal `hashOf` are the same pair. -/
theorem hashOf_pair_inj_of_eq {SF : EVMState}
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    {a b c d : UInt256}
    (hc₁ : ∃ r, Finmap.lookup (accInterval SF a b) SF.keccak_map = some r)
    (hc₂ : ∃ r, Finmap.lookup (accInterval SF c d) SF.keccak_map = some r)
    (heq : hashOf SF a b = hashOf SF c d) :
    a = c ∧ b = d := by
  obtain ⟨r₁, hr₁⟩ := hc₁
  obtain ⟨r₂, hr₂⟩ := hc₂
  rw [hashOf_eq_of_cached hr₁, hashOf_eq_of_cached hr₂] at heq
  subst heq
  exact hashOf_pair_inj hcinj hr₁ hr₂

end Clear.CachedHashInj
