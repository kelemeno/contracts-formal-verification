import Clear.ReasoningPrinciple
import specs.KeccakDeterminism

/-
  THE CALLDATACOPY FRAME.

  Clear models `calldatacopy` faithfully: a byte-wise `updateMemory` fold
  over the extracted calldata (`ByteArray.foldl`, an index-countdown loop).
  This file provides the missing induction bridge and proves the frame law:
  a copy never changes any word STRICTLY BELOW its target — so length words
  and heads written before an abi-encode's element copies survive them.
  This is what lets fixed-offset readbacks (the #43/#44 pinning technique)
  pass through dynamic-array tails.

  Axiom-free.
-/

namespace Clear.CalldatacopyFrame

open Clear EVMState Clear.KeccakDeterminism

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

/-- The copy's byte step. -/
private def copyStep : (EVMState × UInt256) → UInt8 → (EVMState × UInt256) :=
  fun p i => (EVMState.updateMemory p.1 p.2 i.val, p.2 + 1)

/-- The countdown loop of the copy fold leaves every word strictly below the
write cursor unchanged. -/
private lemma loop_frame :
    ∀ (i : ℕ) (as : ByteArray) (stop : ℕ) (h : stop ≤ as.size) (j : ℕ)
      (σa : EVMState) (jj r : UInt256),
    r.val + 32 ≤ jj.val → jj.val + i + 31 ≤ 2 ^ 256 →
    ((ByteArray.foldlM.loop (m := Id) copyStep as stop h i j (σa, jj)).1).machine_state.lookupMemory r
      = σa.machine_state.lookupMemory r := by
  intro i
  induction i with
  | zero =>
    intro as stop h j σa jj r _ _
    unfold ByteArray.foldlM.loop
    split <;> rfl
  | succ i' ih =>
    intro as stop h j σa jj r hr hnw
    unfold ByteArray.foldlM.loop
    split
    · -- one byte written at `jj`, recurse at `jj + 1`
      have hs : UInt256.size = 2 ^ 256 := by norm_num
      have hj1 : (jj + 1).val = jj.val + 1 := by
        have h1 : ((1 : UInt256)).val = 1 := by decide
        rw [Fin.val_add, h1]
        exact Nat.mod_eq_of_lt (by omega)
      show ((ByteArray.foldlM.loop (m := Id) copyStep as stop h i' (j+1)
          (copyStep (σa, jj) _)).1).machine_state.lookupMemory r = _
      rw [show copyStep (σa, jj) (as.get ⟨j, by omega⟩)
          = (σa.updateMemory jj (↑(as.get ⟨j, by omega⟩).val), jj + 1) from rfl]
      rw [ih as stop h (j+1) (σa.updateMemory jj _) (jj + 1) r (by omega) (by omega)]
      show (σa.machine_state.updateMemory jj _).lookupMemory r = _
      exact lookupMemory_updateMemory_outside _ jj _ r
        (by omega) (by omega) (by left; omega)
    · rfl

/-- **THE COPY FRAME.**  `calldatacopy mstart _ s` leaves every word strictly
below `mstart` unchanged. -/
theorem lookupMemory_calldatacopy_below
    {σ : EVMState} {mstart datastart s r : UInt256}
    (hr : r.val + 32 ≤ mstart.val)
    (hnw : mstart.val
        + (ByteArray.extractBytes datastart.val s.val σ.execution_env.input_data).size
        + 31 ≤ 2 ^ 256) :
    (σ.calldatacopy mstart datastart s).machine_state.lookupMemory r
      = σ.machine_state.lookupMemory r := by
  unfold EVMState.calldatacopy
  show ((ByteArray.foldl
      (fun (p : EVMState × UInt256) i => (EVMState.updateMemory p.1 p.2 i.val, p.2 + 1))
      (σ, mstart)
      (ByteArray.extractBytes datastart.val s.val σ.execution_env.input_data)).1).machine_state.lookupMemory r
      = σ.machine_state.lookupMemory r
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [dif_pos (Nat.le_refl _)]
  exact loop_frame _ _ _ _ _ σ mstart r hr (by
    have := hnw
    omega)


/-- The copy loop never touches the execution environment. -/
private lemma loop_env :
    ∀ (i : ℕ) (as : ByteArray) (stop : ℕ) (h : stop ≤ as.size) (j : ℕ)
      (σa : EVMState) (jj : UInt256),
    ((ByteArray.foldlM.loop (m := Id) copyStep as stop h i j (σa, jj)).1).execution_env
      = σa.execution_env := by
  intro i
  induction i with
  | zero =>
    intro as stop h j σa jj
    unfold ByteArray.foldlM.loop
    split <;> rfl
  | succ i' ih =>
    intro as stop h j σa jj
    unfold ByteArray.foldlM.loop
    split
    · show ((ByteArray.foldlM.loop (m := Id) copyStep as stop h i' (j+1)
          (copyStep (σa, jj) _)).1).execution_env = _
      rw [ih]
      rfl
    · rfl

/-- `calldatacopy` preserves the execution environment (in particular the
calldata itself). -/
theorem execution_env_calldatacopy
    (σ : EVMState) (mstart datastart s : UInt256) :
    (σ.calldatacopy mstart datastart s).execution_env = σ.execution_env := by
  unfold EVMState.calldatacopy
  show ((ByteArray.foldl
      (fun (p : EVMState × UInt256) i => (EVMState.updateMemory p.1 p.2 i.val, p.2 + 1))
      (σ, mstart) _).1).execution_env = σ.execution_env
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [dif_pos (Nat.le_refl _)]
  exact loop_env _ _ _ _ _ σ mstart

/-- `mstore` preserves the execution environment. -/
theorem execution_env_mstore (σ : EVMState) (a v : UInt256) :
    (σ.mstore a v).execution_env = σ.execution_env := rfl

/-- **The copy frame, `mload` form**: `calldatacopy mstart _ s` leaves the
word read strictly below `mstart` unchanged. -/
theorem mload_calldatacopy_below
    {σ : EVMState} {mstart datastart s r : UInt256}
    (hr : r.val + 32 ≤ mstart.val)
    (hnw : mstart.val
        + (ByteArray.extractBytes datastart.val s.val σ.execution_env.input_data).size
        + 31 ≤ 2 ^ 256) :
    (σ.calldatacopy mstart datastart s).mload r = σ.mload r := by
  show (σ.calldatacopy mstart datastart s).machine_state.lookupMemory r
    = σ.machine_state.lookupMemory r
  exact lookupMemory_calldatacopy_below hr hnw

end Clear.CalldatacopyFrame
