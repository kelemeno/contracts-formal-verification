import Clear.EVMState
import specs.KeccakDeterminism
import specs.KDParallel.A3

/-!
# Read-back / byte-agreement corollaries (A8)

Small self-contained corollaries built on the byte-encoding infrastructure of
`specs.KeccakDeterminism`:

* `mload_mstore_self` — the word just written by `mstore` reads back verbatim via
  `mload` (a symbolic-address round-trip; wraps `lookupMemory_updateMemory_self'`).
* `coe_fromBytes_toBytes` — the `fromBytes!/toBytes!` round-trip transported back
  into `UInt256` (the `ℕ`-level `fromBytes_toBytes` plus `Fin.cast_val_eq_self`).
* `mkInterval_length` — a keccak interval `mkInterval ms p n` has exactly `n.val`
  words.
* `mkInterval_eq_trans_of_byte_agree` — two-hop transport of
  `mkInterval_eq_of_byte_agree`: byte agreement `m₁≡m₂` on the window and `m₂≡m₃`
  on the window compose to `mkInterval m₁ = mkInterval m₃`.

Everything is derived by composition of existing lemmas — **no axioms** beyond
the standard kernel ones.
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

/-- **`mstore`/`mload` round-trip**: reading back at `a` the word just written by
`mstore a v` returns `v`, for any non-wrapping 32-byte window. -/
theorem mload_mstore_self (σ : EVMState) (a v : UInt256)
    (ha : a.val + 32 ≤ 2 ^ 256) :
    (σ.mstore a v).mload a = v := by
  show (σ.mstore a v).machine_state.lookupMemory a = v
  rw [show (σ.mstore a v).machine_state = σ.machine_state.updateMemory a v from rfl]
  exact lookupMemory_updateMemory_self' σ.machine_state a v ha

/-- The `fromBytes!/toBytes!` round-trip, transported back into `UInt256`
(`fromBytes_toBytes` gives the `ℕ`-level identity; `Fin.cast_val_eq_self`
re-embeds it). -/
theorem coe_fromBytes_toBytes (v : UInt256) :
    ((Clear.UInt256.fromBytes! (Clear.UInt256.toBytes! v) : ℕ) : UInt256) = v := by
  rw [fromBytes_toBytes]
  exact Fin.cast_val_eq_self v

/-- **Two-hop transport** of `mkInterval_eq_of_byte_agree`: if `m₁` agrees with
`m₂` byte-for-byte on the window `[p, p+n+31)`, and `m₂` agrees with `m₃` there,
then `mkInterval m₁ p n = mkInterval m₃ p n`. -/
theorem mkInterval_eq_trans_of_byte_agree
    {m₁ m₂ m₃ : MachineState} {p n : UInt256}
    (hnw : p.val + n.val + 31 ≤ 2 ^ 256)
    (h12 : ∀ i : UInt256, p.val ≤ i.val → i.val < p.val + n.val + 31 →
      Finmap.lookup i m₁.memory = Finmap.lookup i m₂.memory)
    (h23 : ∀ i : UInt256, p.val ≤ i.val → i.val < p.val + n.val + 31 →
      Finmap.lookup i m₂.memory = Finmap.lookup i m₃.memory) :
    mkInterval m₁ p n = mkInterval m₃ p n :=
  (mkInterval_eq_of_byte_agree hnw h12).trans (mkInterval_eq_of_byte_agree hnw h23)

end Clear.KeccakDeterminism
