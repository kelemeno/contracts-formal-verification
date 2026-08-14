import Clear.ReasoningPrinciple
import specs.KeccakDeterminism
import specs.KeccakLowSlot
import specs.KeccakFresh
import specs.KeccakSlotSep

/-! # What does NOT touch storage

`sload` reads one thing: the `code_owner` account in `account_map`.  Every other component
of `EVMState` — memory, the keccak cache, the collision flag — is irrelevant to it.

That is obvious from the definitions and completely invisible to a proof, because the
operations that touch those components appear all through a compiled function body: the
storage-array accessor `mstore`s its argument and hashes it, `fun_efficientHash` `mstore`s
two words and hashes them, and each of those returns a DIFFERENT `EVMState` than it was
given.  Without the lemmas below, a proof that some slot survived a function call has to
stop at the first `mstore`.

So: `sload` passes through `mstore` and through `keccakOut`, unconditionally.  Together
with `KeccakDistinct.sload_sstore_of_ne` (the non-aliasing lemma for the one operation that
DOES write storage) this is everything needed to carry a slot's value across a call.
-/

namespace Clear.StorageFrame

open Clear Clear.KeccakDeterminism Clear.KeccakLowSlot Clear.KeccakSlotSep Clear.KeccakFresh

/-- `mstore` writes MEMORY.  Storage is untouched, so any `sload` reads back the same. -/
@[simp] theorem sload_mstore (σ : EVMState) (a v q : UInt256) :
    (σ.mstore a v).sload q = σ.sload q := by
  unfold EVMState.mstore EVMState.updateMemory EVMState.sload EVMState.lookupAccount
  rfl

/-- Hashing does not write storage either.

`keccak256` either finds the interval in its cache and returns the state UNCHANGED, or
mints a fresh value and updates `keccak_map` / `keccak_range` / `used_range`; the failure
branch only sets `hash_collision`.  None of those is `account_map`, so `sload` survives all
three. -/
@[simp] theorem sload_keccakOut (σ : EVMState) (p n q : UInt256) :
    (keccakOut σ p n).2.sload q = σ.sload q := by
  -- case on `keccak256` FIRST: splitting `keccakOut`'s match leaves the nested one
  -- unevaluated and the resulting state opaque
  unfold keccakOut
  rcases hk : σ.keccak256 p n with _ | ⟨r, σ'⟩
  · simp [EVMState.addHashCollision, EVMState.sload, EVMState.lookupAccount]
  · simp only
    unfold EVMState.keccak256 at hk
    -- zeta-reduce the `let interval := …`: while it stands, the lookup is under a binder
    -- and no rewrite can see it
    dsimp only at hk
    -- `split at hk` picks the INNER match (the partition) first, which leaves the outer
    -- lookup unresolved -- so name the outer scrutinee and rewrite with it instead
    rcases hlk : Finmap.lookup (EVMState.mkInterval σ.machine_state p n) σ.keccak_map with
      _ | val
    · rw [hlk] at hk
      rcases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
        ⟨fst, rest⟩
      rcases rest with _ | ⟨r', rs'⟩
      · rw [hpart] at hk; simp at hk
      · rw [hpart] at hk
        -- fresh value minted: keccak_map / keccak_range / used_range, not account_map
        simp only [Option.some.injEq, Prod.mk.injEq] at hk
        rw [← hk.2]
        simp [EVMState.sload, EVMState.lookupAccount]
    · -- cache hit: the state comes back unchanged
      rw [hlk] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      rw [← hk.2]


/-- Returning does not write storage: it only sets return data in the machine state. -/
@[simp] theorem sload_evm_return (σ : EVMState) (p n q : UInt256) :
    (σ.evm_return p n).sload q = σ.sload q := by
  unfold EVMState.evm_return EVMState.sload EVMState.lookupAccount
  rfl

/-- **Nor does REVERTING.**  `evm_revert` is `evm_return` plus `reverted := true`, and
neither touches `account_map`.

Worth stating plainly because it is the opposite of the EVM's real semantics, where a
revert undoes storage writes.  Clear's `EVMState` models a revert as a FLAG: the state
carries `reverted = true` and its storage is whatever it was.  So a proof may carry a slot
value across a reverting call -- and, conversely, must never read this as "the write was
undone".  What it buys here is that a bounds-check panic needs no special case: `sload`
survives both branches. -/
@[simp] theorem sload_evm_revert (σ : EVMState) (p n q : UInt256) :
    (σ.evm_revert p n).sload q = σ.sload q := by
  unfold EVMState.evm_revert
  -- `{… with reverted := true}` leaves account_map and execution_env alone, so `sload` of
  -- it is definitionally `sload` of the returned state
  show (σ.evm_return p n).sload q = σ.sload q
  exact sload_evm_return σ p n q


/-! ## The keccak CONFIGURATION also survives the writes

`RangeInWindow` and `CachedInWindow` quantify over `keccak_range` and `keccak_map`.  A
memory write, a storage write and a revert touch none of those, so the configuration a
low-slot argument depends on is carried across every step of a compiled body -- exactly as
`sload` is above.  `KeccakLowSlot` already covers the hash step itself
(`rangeInWindow_keccakOut`, `cachedInWindow_keccakOut`). -/

theorem rangeInWindow_mstore {σ : EVMState} {a v : UInt256} (h : RangeInWindow σ) :
    RangeInWindow (σ.mstore a v) := h

theorem cachedInWindow_mstore {σ : EVMState} {a v : UInt256} (h : CachedInWindow σ) :
    CachedInWindow (σ.mstore a v) := h

theorem rangeInWindow_sstore {σ : EVMState} {p v : UInt256} (h : RangeInWindow σ) :
    RangeInWindow (σ.sstore p v) := by
  unfold RangeInWindow EVMState.sstore at *
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none => simpa only [hacc] using h
  | some act => simpa only [hacc] using h

theorem cachedInWindow_sstore {σ : EVMState} {p v : UInt256} (h : CachedInWindow σ) :
    CachedInWindow (σ.sstore p v) := by
  unfold CachedInWindow EVMState.sstore at *
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none => simpa only [hacc] using h
  | some act => simpa only [hacc] using h

theorem rangeInWindow_evm_revert {σ : EVMState} {p n : UInt256} (h : RangeInWindow σ) :
    RangeInWindow (σ.evm_revert p n) := h

theorem cachedInWindow_evm_revert {σ : EVMState} {p n : UInt256} (h : CachedInWindow σ) :
    CachedInWindow (σ.evm_revert p n) := h


/-! ## The SEPARATION configuration survives the writes too

`Separated`, `CacheInj` and `CacheInUsed` quantify over `keccak_map`, `keccak_range` and
`used_range` -- again none of them memory or storage.  `KeccakSlotSep` and `KeccakFresh`
cover the hash step (`separated_keccakOut`, `cacheInj_keccakOut`); these cover everything
else a compiled body does, so the hypotheses of `cached_off_ne_off` can be carried from a
caller's `s₀` to the state where the fold actually hashes.

That matters for the array-LENGTH half of the accessor's bounds hypothesis: a length slot
is itself `keccak(nodes) + i`, so ruling out a collision with the written node slot is an
offset-vs-offset question, which is what `cached_off_ne_off` answers. -/

theorem separated_mstore {σ : EVMState} {a v : UInt256} (h : Separated σ) :
    Separated (σ.mstore a v) := h

theorem separated_evm_revert {σ : EVMState} {p n : UInt256} (h : Separated σ) :
    Separated (σ.evm_revert p n) := h

theorem separated_sstore {σ : EVMState} {p v : UInt256} (h : Separated σ) :
    Separated (σ.sstore p v) := by
  unfold Separated Slots EVMState.sstore at *
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none => simpa only [hacc] using h
  | some act => simpa only [hacc] using h

theorem cacheInj_mstore {σ : EVMState} {a v : UInt256} (h : CacheInj σ) :
    CacheInj (σ.mstore a v) := h

theorem cacheInj_evm_revert {σ : EVMState} {p n : UInt256} (h : CacheInj σ) :
    CacheInj (σ.evm_revert p n) := h

theorem cacheInj_sstore {σ : EVMState} {p v : UInt256} (h : CacheInj σ) :
    CacheInj (σ.sstore p v) := by
  unfold CacheInj EVMState.sstore at *
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none => simpa only [hacc] using h
  | some act => simpa only [hacc] using h

theorem cacheInUsed_mstore {σ : EVMState} {a v : UInt256} (h : CacheInUsed σ) :
    CacheInUsed (σ.mstore a v) := h

theorem cacheInUsed_evm_revert {σ : EVMState} {p n : UInt256} (h : CacheInUsed σ) :
    CacheInUsed (σ.evm_revert p n) := h

/-- NOTE the asymmetry: `sstore` DOES touch the keccak state -- it adds the written slot to
`used_range`.  `Separated` and `CacheInj` do not mention `used_range` and so are literally
unchanged, but `CacheInUsed` needs the (easy) monotonicity step: the set only GROWS, so a
value already in it stays in it.  "A storage write does not touch the keccak model" would
have been the wrong claim. -/
theorem cacheInUsed_sstore {σ : EVMState} {p v : UInt256} (h : CacheInUsed σ) :
    CacheInUsed (σ.sstore p v) := by
  unfold CacheInUsed EVMState.sstore at *
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none => simpa only [hacc] using h
  | some act =>
    simp only [hacc]
    intro I w hlk
    exact Finset.mem_union_right _ (h I w hlk)

end Clear.StorageFrame
