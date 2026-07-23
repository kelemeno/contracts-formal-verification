import Clear.EVMState
import specs.KeccakDeterminism

/-!
# Structural facts about `window` and `mkInterval` (A3)

Small, self-contained structural lemmas about the 32-byte address list
`window a = [a, a+1, …, a+31]` and the accessor interval `mkInterval ms p n`.
Everything is derived by unfolding the definitions and `simp`/`decide` —
**no axioms** beyond the standard kernel ones.
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

/-- `window a` always has exactly 32 entries. -/
theorem window_length (a : UInt256) : (window a).length = 32 := by
  unfold window
  simp

/-- `window 64` has no duplicates (mirrors `window_32_nodup`). -/
theorem window_64_nodup : (window (64 : UInt256)).Nodup := by decide

/-- The base address `a` is the head element of `window a`. -/
theorem self_mem_window (a : UInt256) : a ∈ window a := by
  unfold window
  rw [List.mem_map]
  exact ⟨0, List.mem_range.mpr (by norm_num), by simp⟩

/-- `window a` is never empty. -/
theorem window_ne_nil (a : UInt256) : window a ≠ [] := by
  intro h
  have : (window a).length = 0 := by rw [h]; rfl
  rw [window_length] at this
  exact absurd this (by norm_num)

/-- The `mkInterval ms p n` address list has length `n.val`. -/
theorem mkInterval_length (ms : MachineState) (p n : UInt256) :
    (mkInterval ms p n).length = n.val := by
  unfold EVMState.mkInterval
  simp

end Clear.KeccakDeterminism
