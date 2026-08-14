import Clear.ReasoningPrinciple
import specs.KeccakDeterminism
import specs.KeccakDistinct
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


/-- **READING BACK WHAT YOU WROTE.**  The companion of
`KeccakDistinct.sload_sstore_of_ne`: at the slot just written, `sload` returns the value.

Two details of Clear's model this makes explicit.  It needs the `code_owner` ACCOUNT TO
EXIST -- with no account `sstore` is a no-op and `sload` returns 0, so the lemma would be
false.  And the account layer stores 0 by ERASING the key
(`lookupStorage_updateStorage_self` returns `if v == 0 then 0 else v`), which happens to
equal `v` in both cases, so the zero-erasure is invisible here -- but it is why this is not
simply `rfl`.

Needed by any "the length went up by one" result: `array.push` does `sstore(array,
oldLen+1)` and the length is read back at that same slot. -/
theorem sload_sstore_self {σ : EVMState} {p v : UInt256} {act : Account}
    (hacc : σ.lookupAccount σ.execution_env.code_owner = some act) :
    (σ.sstore p v).sload p = v := by
  unfold EVMState.sstore EVMState.sload
  simp only [hacc]
  unfold EVMState.lookupAccount EVMState.updateAccount
  simp only [Finmap.lookup_insert]
  rw [Clear.KeccakDistinct.lookupStorage_updateStorage_self]
  by_cases hv : v == 0
  · simp only [hv, if_true]
    exact (beq_iff_eq _ _).mp hv |>.symm
  · simp only [hv, if_false]


/-- **AFTER A PUSH, THE INDEX FITS.**  The old length is strictly below the new one, so the
accessor call that computes the new element's address has its bounds hypothesis satisfied.

`array.push` writes `oldLen + 1` to the length slot and then addresses element `oldLen`;
the address computation bounds-checks against the length it just wrote.  Needs no-wrap,
which the push's own `2 ^ 64` guard supplies. -/
theorem sload_lt_after_push {σ : EVMState} {array : UInt256} {act : Account}
    (hacc : σ.lookupAccount σ.execution_env.code_owner = some act)
    (hfits : (σ.sload array).val + 1 < UInt256.size) :
    σ.sload array < (σ.sstore array (σ.sload array + 1)).sload array := by
  rw [sload_sstore_self hacc]
  have h1 : ((1 : UInt256)).val = 1 := by decide
  have hval : ((σ.sload array) + 1).val = (σ.sload array).val + 1 := by
    rw [Fin.val_add, h1, Nat.mod_eq_of_lt hfits]
  simp only [Fin.lt_def, hval]
  omega
/-! ### The ACCOUNT frame

`sload_sstore_self` -- "a write reads back" -- needs an account to exist at `code_owner`,
and that hypothesis has to survive the calls between the write and the read.  These say it
does: nothing on the array-push path removes the account or changes which address is
`code_owner`.

Without this layer a "the element you wrote is the element that is there" result cannot be
stated at all, because the account hypothesis would have to be assumed at an intermediate
state the caller cannot name. -/

@[simp] theorem lookupAccount_mstore (σ : EVMState) (a v : UInt256) (addr : Address) :
    (σ.mstore a v).lookupAccount addr = σ.lookupAccount addr := rfl

@[simp] theorem execution_env_mstore (σ : EVMState) (a v : UInt256) :
    (σ.mstore a v).execution_env = σ.execution_env := rfl

/-- Hashing mints a fresh slot value or hits the cache; either way it rewrites the keccak
tables, never `account_map` or `execution_env`.  Same case structure as
`sload_keccakOut`: split `keccak256` FIRST, then the cache lookup, then the partition. -/
theorem keccakOut_frame (σ : EVMState) (p n : UInt256) :
    (keccakOut σ p n).2.account_map = σ.account_map ∧
      (keccakOut σ p n).2.execution_env = σ.execution_env := by
  unfold keccakOut
  rcases hk : σ.keccak256 p n with _ | ⟨r, σ'⟩
  · exact ⟨rfl, rfl⟩
  · simp only
    unfold EVMState.keccak256 at hk
    dsimp only at hk
    rcases hlk : Finmap.lookup (EVMState.mkInterval σ.machine_state p n) σ.keccak_map with
      _ | val
    · rw [hlk] at hk
      rcases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
        ⟨fst, rest⟩
      rcases rest with _ | ⟨r', rs'⟩
      · rw [hpart] at hk; simp at hk
      · rw [hpart] at hk
        simp only [Option.some.injEq, Prod.mk.injEq] at hk
        rw [← hk.2]
        exact ⟨rfl, rfl⟩
    · rw [hlk] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      rw [← hk.2]
      exact ⟨rfl, rfl⟩

theorem lookupAccount_keccakOut (σ : EVMState) (p n : UInt256) (addr : Address) :
    (keccakOut σ p n).2.lookupAccount addr = σ.lookupAccount addr := by
  unfold EVMState.lookupAccount
  rw [(keccakOut_frame σ p n).1]

@[simp] theorem execution_env_keccakOut (σ : EVMState) (p n : UInt256) :
    (keccakOut σ p n).2.execution_env = σ.execution_env := (keccakOut_frame σ p n).2

@[simp] theorem execution_env_evm_revert (σ : EVMState) (p n : UInt256) :
    (σ.evm_revert p n).execution_env = σ.execution_env := rfl

@[simp] theorem lookupAccount_evm_revert (σ : EVMState) (p n : UInt256) (addr : Address) :
    (σ.evm_revert p n).lookupAccount addr = σ.lookupAccount addr := rfl

/-- **The account survives a write to it** -- indeed `sstore` is what updates it.  This is
the step that lets the account hypothesis cross `array.push`'s length write and still be
available for the element write that follows. -/
theorem lookupAccount_sstore_self {σ : EVMState} {p v : UInt256} {act : Account}
    (hacc : σ.lookupAccount σ.execution_env.code_owner = some act) :
    (σ.sstore p v).lookupAccount (σ.sstore p v).execution_env.code_owner
      = some (act.updateStorage p v) := by
  unfold EVMState.sstore
  simp only [hacc]
  unfold EVMState.lookupAccount EVMState.updateAccount
  simp only [Finmap.lookup_insert]

end Clear.StorageFrame
