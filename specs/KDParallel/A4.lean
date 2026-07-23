import Clear.EVMState
import specs.KeccakDeterminism

/-!
# `keccakOut` memory-frame facts (KDParallel A4)

`keccakOut` hashes but never writes memory. This file records the memory-frame
consequences of `keccakOut_machine_state` (memory unchanged): the word-level
`mload` frame, the byte-level `Finmap.lookup` frame, and a two-step cache
monotonicity fact composed from `keccakOut_lookup_mono`. Axiom-free.
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- `keccakOut` leaves every `mload` unchanged (it never writes memory). -/
theorem keccakOut_mload (σ : EVMState) (p n a : UInt256) :
    (keccakOut σ p n).2.mload a = σ.mload a := by
  simp only [EVMState.mload, keccakOut_machine_state]

/-- `keccakOut` leaves every byte-level memory `Finmap.lookup` unchanged. -/
theorem keccakOut_lookup_mem (σ : EVMState) (p n : UInt256) (i : UInt256) :
    Finmap.lookup i (keccakOut σ p n).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  rw [keccakOut_machine_state]

/-- A cache entry survives TWO consecutive `keccakOut` steps. -/
theorem keccakOut_lookup_mono₂
    {σ : EVMState} {p₁ n₁ p₂ n₂ : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (keccakOut (keccakOut σ p₁ n₁).2 p₂ n₂).2.keccak_map = some w :=
  keccakOut_lookup_mono (keccakOut_lookup_mono hI)

end Clear.KeccakDeterminism
