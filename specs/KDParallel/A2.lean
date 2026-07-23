import Clear.EVMState
import specs.KeccakDeterminism

/-!
# Chained accOut cache/collision frame lemmas (A2)

Two- and three-step compositions of the one-step `accOut` frame lemmas from
`specs.KeccakDeterminism`:

* `accOut_lookup_mono₂` / `accOut_lookup_mono₃` — an existing keccak-cache entry
  survives two / three consecutive `accOut` steps (compose `accOut_lookup_mono`).
* `accOut_clean_backward₂` — a collision-free post-state of two consecutive
  `accOut` steps forces a collision-free original input (compose
  `accOut_clean_backward` twice, mind the nesting).

Everything is derived from the one-step lemmas: **no axioms** beyond the standard
kernel ones.
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- `accOut` preserves existing cache entries across TWO consecutive steps. -/
theorem accOut_lookup_mono₂
    {σ : EVMState} {k₁ b₁ k₂ b₂ : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (accOut (accOut σ k₁ b₁).2 k₂ b₂).2.keccak_map = some w :=
  accOut_lookup_mono (accOut_lookup_mono hI)

/-- `accOut` preserves existing cache entries across THREE consecutive steps. -/
theorem accOut_lookup_mono₃
    {σ : EVMState} {k₁ b₁ k₂ b₂ k₃ b₃ : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I
        (accOut (accOut (accOut σ k₁ b₁).2 k₂ b₂).2 k₃ b₃).2.keccak_map = some w :=
  accOut_lookup_mono (accOut_lookup_mono (accOut_lookup_mono hI))

/-- A collision-free post-state of TWO consecutive `accOut` steps forces a
collision-free input state. -/
theorem accOut_clean_backward₂
    {σ : EVMState} {k₁ b₁ k₂ b₂ : UInt256}
    (h : (accOut (accOut σ k₁ b₁).2 k₂ b₂).2.hash_collision = false) :
    σ.hash_collision = false :=
  accOut_clean_backward (accOut_clean_backward h)

end Clear.KeccakDeterminism
