import Clear.EVMState
import specs.KeccakDeterminism

/-!
# `mstore`/`mload` frame lemmas (KDParallel A6)

EVMState-level word-and-byte framing for a single 32-byte `mstore`. `mstore b v`
is `updateMemory b v` on `machine_state`; `mload a` is `lookupMemory a`. These
lift the `MachineState` lemmas (`lookupMemory_updateMemory_outside`,
`lookup_updateMemory_outside_val`) to the `EVMState` wrapper: reads at a word
disjoint (above or below) from the written 32-byte window are unchanged, and a
write into the scratch region `[0, 64)` leaves the junk window `[64, …)` intact.
Axiom-free.
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- **High-side `mload` frame**: a write of `v` at `b` is invisible to a word
read at `a` sitting at least 32 bytes above the write (`b.val + 32 ≤ a.val`),
provided `a`'s own window does not wrap (`a.val + 32 ≤ 2^256`). -/
theorem mload_mstore_high (σ : EVMState) (a b v : UInt256)
    (hba : b.val + 32 ≤ a.val) (ha : a.val + 32 ≤ 2 ^ 256) :
    (σ.mstore b v).mload a = σ.mload a := by
  show (σ.machine_state.updateMemory b v).lookupMemory a
      = σ.machine_state.lookupMemory a
  exact lookupMemory_updateMemory_outside σ.machine_state b v a
    (by omega) ha (by right; omega)

/-- **Low-side `mload` frame**: a write of `v` at `b` is invisible to a word read
at `a` sitting at least 32 bytes below the write (`a.val + 32 ≤ b.val`), provided
`b`'s own window does not wrap (`b.val + 32 ≤ 2^256`). -/
theorem mload_mstore_low (σ : EVMState) (a b v : UInt256)
    (hab : a.val + 32 ≤ b.val) (hb : b.val + 32 ≤ 2 ^ 256) :
    (σ.mstore b v).mload a = σ.mload a := by
  show (σ.machine_state.updateMemory b v).lookupMemory a
      = σ.machine_state.lookupMemory a
  exact lookupMemory_updateMemory_outside σ.machine_state b v a
    hb (by omega) (by left; omega)

/-- **Scratch-write junk frame**: a write inside the scratch region `[0, 64)`
(`b.val + 32 ≤ 64`) leaves every byte at `64 ≤ i.val` unchanged. -/
theorem mstore_junk_generic {σ : EVMState} {b v : UInt256} {i : UInt256}
    (hb : b.val + 32 ≤ 64) (hi : 64 ≤ i.val) :
    Finmap.lookup i (σ.mstore b v).machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  apply lookup_updateMemory_outside_val
  · omega
  · right; omega

end Clear.KeccakDeterminism
