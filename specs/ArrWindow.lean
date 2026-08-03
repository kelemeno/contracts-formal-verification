import specs.KeccakDeterminism

/-
  R0 — THE 32-BYTE ACCESSOR WINDOW TRANSPORT KIT.

  `ROOT_FIDELITY_BLUEPRINT.md` stage R0.  The storage-array accessor hashes the
  32-byte scratch word at address 0 (`mstore(0, a); keccak256(0, 32)`), so its
  keccak cache key is `mkInterval m 0 32`.  That interval reads 32 WORDS at byte
  addresses `0 … 31`, and a word read at `i` spans bytes `[i, i+32)`, so the
  interval depends on exactly memory bytes `[0, 63)`:

      bytes [0, 32)   pinned by the `mstore 0 a` itself
      bytes [32, 63)  JUNK inherited from the surrounding state

  This file proves when that window is stable.  The pattern mirrors
  `accInterval_eq` for the 64-byte accessor, but the boundary sits at 63 rather
  than 95, which is why the two kits are separate.

  * `arrWindow_eq_of_byte_agree` — the window is determined by bytes `[0, 63)`.
  * `arrWindow_mstore_high` — INVARIANT under a memory write at address ≥ 63
    (in particular every allocator bump, which writes at ≥ 64).
  * `arrWindow_eq_of_mem_eq` — invariant whenever the memory map is unchanged,
    which covers `sstore` and any keccak step (neither touches memory).

  THE ANCHOR BOUNDARY, deliberately without a lemma: a write at address 32 DOES
  move the window, since it overwrites the junk bytes `[32, 63)`.  Every pair-hash
  step (`mstore 0 _; mstore 32 _; keccak`) therefore invalidates every array
  accessor cache key — that is the churn the blueprint calls its single biggest
  cost driver, and no lemma here can hide it.

  Axiom-free: byte-window arithmetic only, on top of `KeccakDeterminism`.
-/

namespace Clear.ArrWindow

open Clear Clear.KeccakDeterminism EVMState

/-- The accessor's cache key: the 32-byte window at address 0. -/
def arrWindow (m : MachineState) : List UInt256 := mkInterval m 0 32

/-- **THE WINDOW IS DETERMINED BY BYTES `[0, 63)`.**  Specialisation of
`mkInterval_eq_of_byte_agree` to the 32-word accessor window. -/
theorem arrWindow_eq_of_byte_agree {m₁ m₂ : MachineState}
    (hagree : ∀ i : UInt256, i.val < 63 →
      Finmap.lookup i m₁.memory = Finmap.lookup i m₂.memory) :
    arrWindow m₁ = arrWindow m₂ := by
  unfold arrWindow
  refine mkInterval_eq_of_byte_agree ?_ ?_
  · have h32 : ((32 : UInt256)).val = 32 := by decide
    have h0 : ((0 : UInt256)).val = 0 := by decide
    rw [h0, h32]; norm_num
  intro i _ hi
  exact hagree i (by simpa using hi)

/-- **INVARIANT UNDER A HIGH MEMORY WRITE.**  A 32-byte store at any address
`≥ 63` misses the window entirely — this is the allocator-bump case, since bumps
write at `≥ 64`. -/
theorem arrWindow_mstore_high {m : MachineState} {a v : UInt256}
    (ha : 63 ≤ a.val) (hnw : a.val + 32 ≤ 2 ^ 256) :
    arrWindow (m.updateMemory a v) = arrWindow m := by
  refine arrWindow_eq_of_byte_agree ?_
  intro i hi
  exact lookup_updateMemory_outside_val m a v i hnw (Or.inl (by omega))

/-- **INVARIANT UNDER ANYTHING THAT LEAVES MEMORY ALONE.**  Covers `sstore` and
every keccak step: neither writes memory, so the accessor's cache key cannot
move. -/
theorem arrWindow_eq_of_mem_eq {m₁ m₂ : MachineState}
    (hmem : m₁.memory = m₂.memory) :
    arrWindow m₁ = arrWindow m₂ := by
  refine arrWindow_eq_of_byte_agree ?_
  intro i _
  rw [hmem]

/-! ## `EVMState`-level wrappers

R1 consumes the window at the `EVMState` level, so the three facts are restated
there.  `machine_state_sstore` is reproved locally (four lines) rather than widening
the scope of the `private` copy in `imt_replay_user.lean`. -/

/-- The accessor cache key of a whole state. -/
def arrWindowOf (σ : EVMState) : List UInt256 := arrWindow σ.machine_state

/-- `sstore` leaves the machine state alone. -/
private lemma machine_state_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).machine_state = σ.machine_state := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- **`sstore` CANNOT MOVE THE ACCESSOR KEY.**  Storage writes leave memory
untouched, so every array-accessor cache entry survives them — this is what lets
the atlas carry cached slots across the walk's storage traffic. -/
theorem arrWindowOf_sstore (σ : EVMState) (a v : UInt256) :
    arrWindowOf (σ.sstore a v) = arrWindowOf σ := by
  unfold arrWindowOf
  rw [machine_state_sstore]

/-- **A HIGH MEMORY WRITE CANNOT MOVE THE ACCESSOR KEY.**  In particular the
allocator bumps, which write at `≥ 64`. -/
theorem arrWindowOf_mstore_high {σ : EVMState} {a v : UInt256}
    (ha : 63 ≤ a.val) (hnw : a.val + 32 ≤ 2 ^ 256) :
    arrWindowOf (σ.mstore a v) = arrWindowOf σ :=
  arrWindow_mstore_high ha hnw

end Clear.ArrWindow
