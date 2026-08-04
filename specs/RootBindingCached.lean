import specs.MerkleCachedInj
import specs.CachedHashInj

/-
  M-D, INSTANTIATED WITH THE DEPLOYED HASH.

  `specs/MerkleCachedInj.lean` restricted M-D's node-hash injectivity to a predicate `P` holding
  on the pairs the tree's own levels hash.  It asserted that the deployed hash can instantiate
  that.  This file PROVES it, so the claim is machine-checked rather than editorial.

  `P` is "this pair's accessor preimage is in `SF`'s keccak cache".  Injectivity on such pairs is
  `CachedHashInj.hashOf_pair_inj`, itself derived from keccak cache injectivity alone.  The
  resulting obligation is: the reference state hashed every adjacent pair of every level of both
  leaf lists — linear in the tree size, and exactly what a builder run establishes by having built
  the tree.  Axiom-free.
-/

namespace Clear.RootBindingCached

open Clear Clear.KeccakDeterminism Clear.CachedHash Clear.CachedHashInj Clear.MerkleCachedInj
open MerkleSpec

/-- A pair whose accessor preimage the reference state has hashed. -/
def CachedPair (SF : EVMState) : UInt256 → UInt256 → Prop :=
  fun a b => ∃ r : UInt256, Finmap.lookup (accInterval SF a b) SF.keccak_map = some r

/-- The deployed hash is pair-injective on cached pairs — `hashOf_pair_inj` in the shape
`MerkleCachedInj` consumes. -/
theorem hashOf_inj_on_cached {SF : EVMState}
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J) :
    ∀ a b c d : UInt256, CachedPair SF a b → CachedPair SF c d →
      hashOf SF a b = hashOf SF c d → a = c ∧ b = d := by
  intro a b c d hab hcd heq
  exact hashOf_pair_inj_of_eq hcinj hab hcd heq

/-- **M-D FOR THE DEPLOYED HASH.**  Same width, same published root, and the reference state
hashed every pair of both trees' levels ⟹ same leaves.

The only cryptographic hypothesis is `hcinj`: keccak is injective on the preimages it has hashed.
No abstract node hash appears, and nothing is assumed at uncached arguments. -/
theorem rootOf_inj_cached {SF : EVMState} (z0 : UInt256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height,
      PairsOK (CachedPair SF) (zeros (hashOf SF) z0 l) (levels (hashOf SF) z0 L₁ l))
    (hp₂ : ∀ l < height,
      PairsOK (CachedPair SF) (zeros (hashOf SF) z0 l) (levels (hashOf SF) z0 L₂ l))
    (hroot : rootOf (hashOf SF) z0 L₁ height = rootOf (hashOf SF) z0 L₂ height) :
    L₁ = L₂ :=
  rootOf_inj_on (hashOf SF) z0 (hashOf_inj_on_cached hcinj) L₁ L₂ height hlen hne hcap hp₁ hp₂ hroot

/-- **ENTRY-LEVEL FORM.**  Equal published roots force equal entries at every index, for the
deployed hash.  This is the shape root binding consumes: `AttackVectors.LeafDecode3`'s
`root_binding` chain takes exactly `getD` agreement at the opened index. -/
theorem getD_of_rootOf_eq_cached {SF : EVMState} (z0 : UInt256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height,
      PairsOK (CachedPair SF) (zeros (hashOf SF) z0 l) (levels (hashOf SF) z0 L₁ l))
    (hp₂ : ∀ l < height,
      PairsOK (CachedPair SF) (zeros (hashOf SF) z0 l) (levels (hashOf SF) z0 L₂ l))
    (hroot : rootOf (hashOf SF) z0 L₁ height = rootOf (hashOf SF) z0 L₂ height)
    (i : ℕ) (dflt : UInt256) : L₁.getD i dflt = L₂.getD i dflt := by
  rw [rootOf_inj_cached z0 hcinj L₁ L₂ height hlen hne hcap hp₁ hp₂ hroot]

end Clear.RootBindingCached
