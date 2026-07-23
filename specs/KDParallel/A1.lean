import Clear.EVMState
import specs.KeccakDeterminism

/-!
# Chained accessor-step frame lemmas (A1)

Composes the one-step frame lemmas of `specs.KeccakDeterminism`
(`accOut_junk_window`, `accOut_mload_high`) into three- and two/three-step
chained forms. Everything is derived by `rw`-composition of the existing
one-step lemmas — **no axioms** beyond the standard kernel ones.
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- The junk window `[64, 95)` survives THREE consecutive accessor steps. -/
theorem accOut_junk_window₃
    {σ : EVMState} {k₁ b₁ k₂ b₂ k₃ b₃ : UInt256} {i : UInt256}
    (hi : 64 ≤ i.val) :
    Finmap.lookup i
        (accOut (accOut (accOut σ k₁ b₁).2 k₂ b₂).2 k₃ b₃).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  rw [accOut_junk_window hi, accOut_junk_window hi, accOut_junk_window hi]

/-- A word at `96 ≤ a` survives TWO consecutive accessor steps. -/
theorem accOut_mload_high₂
    {σ : EVMState} {x₁ y₁ x₂ y₂ a : UInt256}
    (ha : 96 ≤ a.val) (hnw : a.val + 32 ≤ 2 ^ 256) :
    (accOut (accOut σ x₁ y₁).2 x₂ y₂).2.mload a = σ.mload a := by
  rw [accOut_mload_high ha hnw, accOut_mload_high ha hnw]

/-- A word at `96 ≤ a` survives THREE consecutive accessor steps. -/
theorem accOut_mload_high₃
    {σ : EVMState} {x₁ y₁ x₂ y₂ x₃ y₃ a : UInt256}
    (ha : 96 ≤ a.val) (hnw : a.val + 32 ≤ 2 ^ 256) :
    (accOut (accOut (accOut σ x₁ y₁).2 x₂ y₂).2 x₃ y₃).2.mload a = σ.mload a := by
  rw [accOut_mload_high ha hnw, accOut_mload_high ha hnw, accOut_mload_high ha hnw]

end Clear.KeccakDeterminism
