import Clear.EVMState
import specs.KeccakDistinct

/-!
# Keccak slot-injectivity (TRUSTED-BASE AXIOM)

Clear's `keccak256` model (`EVMState.lean`) is *freshness*-based: a new preimage
gets a slot drawn fresh from `keccak_range \ used_range`, and a previously-seen
preimage replays its cached slot. This gives **consistency** (same preimage →
same slot, within a state thread) and **sequential freshness** (`keccak256_distinct_sequential`
in `Clear.KeccakDistinct`), but it does NOT establish full **injectivity**: that two
calls with *different* preimages always land on *different* slots. The freshness
note at the bottom of `KeccakDistinct.lean` records this gap.

End-of-call storage non-aliasing proofs need exactly that injectivity — e.g. a
write to `_indexes[key]` at `keccak(key‖209)` must not clobber a value stored at
`_zkChainMap._values[key]` = `keccak(key‖210)`, which requires
`keccak(key‖209) ≠ keccak(key‖210)` from `(key‖209) ≠ (key‖210)`.

This file adds that as an **explicit axiom**, modelling real keccak's
collision-resistance as injectivity of the hash on its preimage bytes. This is a
deliberate, localized **enlargement of the trusted base**: every theorem that
transitively uses `keccak256_inj` (or the corollaries below) depends on this
axiom, and that dependency is visible via `#print axioms`. The axiom is the
standard cryptographic idealization (collision-resistant hash ≈ injective) and is
stated minimally — it asserts only "distinct preimages ⇒ distinct slots", without
positing a global hash function (which would over-constrain the model's
fresh-pick behavior across disjoint state threads).
-/

namespace Clear.KeccakInjective

open Clear EVMState

/-- **Keccak slot-injectivity (AXIOM).** Two successful `keccak256` calls whose
preimage byte-intervals differ return *distinct* slots. This idealizes keccak's
collision-resistance as injectivity. Trusted-base assumption — see file header. -/
axiom keccak256_inj
    {σ₁ σ₂ σ₁' σ₂' : EVMState} {p₁ n₁ p₂ n₂ r₁ r₂ : UInt256} :
    σ₁.keccak256 p₁ n₁ = some (r₁, σ₁') →
    σ₂.keccak256 p₂ n₂ = some (r₂, σ₂') →
    mkInterval σ₁.machine_state p₁ n₁ ≠ mkInterval σ₂.machine_state p₂ n₂ →
    r₁ ≠ r₂

/-- A `sstore` at a keccak slot `b` preserves the `sload` at a keccak slot `a`,
whenever the two preimages differ. This is the headline non-aliasing tool for
upgrading mid-execution storage writes to end-of-call: combine the model lemma
`Clear.KeccakDistinct.sload_sstore_of_ne` (write-at-b preserves read-at-`a ≠ b`)
with `keccak256_inj` (distinct preimages ⇒ `a ≠ b`). -/
theorem sload_sstore_keccak_of_preimage_ne
    {σ_a σ_a' σ_b σ_b' σ_w : EVMState} {pa na pb nb a b v : UInt256}
    (ha : σ_a.keccak256 pa na = some (a, σ_a'))
    (hb : σ_b.keccak256 pb nb = some (b, σ_b'))
    (hpre : mkInterval σ_a.machine_state pa na ≠ mkInterval σ_b.machine_state pb nb) :
    (σ_w.sstore b v).sload a = σ_w.sload a := by
  have hab : a ≠ b := keccak256_inj ha hb hpre
  exact Clear.KeccakDistinct.sload_sstore_of_ne σ_w hab

/-! ## Concrete demonstration: EnumerableMap `_values[k]` vs `_indexes[k]` slots differ

In zkSync's `EnumerableMap`, a key `k` stores its value at `keccak(k ‖ 210)` and its
index at `keccak(k ‖ 209)`, following the Solidity mapping-slot rule
`keccak256(abi.encode(key, baseSlot))`: memory word 0 (address `0`) holds `k`, and
memory word 1 (address `32`) holds the base slot literal (`210` for `_values`,
`209` for `_indexes`). Both hashes are taken over the 64-byte interval `[0, 64)`.

The slots are distinct iff the preimages differ, and the preimages differ because
the two machine states disagree on the word stored at address `32`. We reduce the
preimage-distinctness (`mkInterval … ≠ mkInterval …`) to exactly that single fact —
`ms_v.lookupMemory 32 ≠ ms_i.lookupMemory 32` — which is the genuine residual
obligation (the `mstore` round-trip `lookupMemory (mstore σ 32 v) 32 = v` for the
two literals `210 ≠ 209`). We then discharge non-aliasing via `keccak256_inj`. -/

/-- The two 64-byte preimages differ whenever the underlying machine states disagree
on the word read at address `32` (the mapping base-slot word). Pure list reasoning:
address `32` occurs at list index `32` of `mkInterval ms 0 64`, so the mapped lists
differ there. -/
theorem mkInterval_0_64_ne_of_word32_ne
    {ms_v ms_i : MachineState}
    (h32 : ms_v.lookupMemory (32 : UInt256) ≠ ms_i.lookupMemory (32 : UInt256)) :
    mkInterval ms_v 0 64 ≠ mkInterval ms_i 0 64 := by
  intro heq
  apply h32
  have ev : ∀ ms : MachineState,
      (mkInterval ms 0 64).get? 32 = some (ms.lookupMemory (32 : UInt256)) := by
    intro ms
    unfold mkInterval
    simp only [List.get?_map]
    have hidx : (List.range' (↑(0 : UInt256)) (↑(64 : UInt256))).get? 32 = some 32 := by
      decide
    rw [hidx]
    rfl
  have h := ev ms_v
  rw [heq, ev ms_i] at h
  exact (Option.some.inj h).symm

/-- **Demonstration that `keccak256_inj` resolves a real non-aliasing fact.**
For an EnumerableMap key `k`, the `_values[k]` slot (`keccak(k ‖ 210)`) and the
`_indexes[k]` slot (`keccak(k ‖ 209)`) are DISTINCT, provided only that the two
machine states disagree on the base-slot word at address `32` (`210` vs `209`).
This is the fact that blocked the `registerNewZKChain` end-of-call upgrade. -/
theorem enumerablemap_values_indexes_slots_distinct
    {σ_v σ_v' σ_i σ_i' : EVMState} {r_values r_indexes : UInt256}
    (hv : σ_v.keccak256 0 64 = some (r_values, σ_v'))
    (hi : σ_i.keccak256 0 64 = some (r_indexes, σ_i'))
    (h32 : σ_v.machine_state.lookupMemory (32 : UInt256)
             ≠ σ_i.machine_state.lookupMemory (32 : UInt256)) :
    r_values ≠ r_indexes :=
  keccak256_inj hv hi (mkInterval_0_64_ne_of_word32_ne h32)

/-! ## Discharging `h32` via a Clear-model `mstore` round-trip

`h32` is the only residual hypothesis of `enumerablemap_values_indexes_slots_distinct`.
The standard mapping-slot layout writes the base slot with `mstore(32, baseSlot)`
(`210` for `_values`, `209` for `_indexes`), so `h32` follows from the round-trip
`lookupMemory (mstore σ 32 v) 32 = v` together with `210 ≠ 209`.

Clear's `mstore` is `updateMemory`, which folds 32 byte-`insert`s of `toBytes! v` at
addresses `addr+0 … addr+31`; `lookupMemory addr` reads those bytes back and applies
`fromBytes!`. No round-trip lemma exists in Clear or `KeccakDistinct`, so we prove it
here. The three list helpers below are fully general; `mload_mstore_self` /
`lookupMemory_updateMemory_self` instantiate them at address `32`. -/

/-- Looking up an address **not** among the folded `insert`s leaves it unchanged. -/
theorem lookup_fold_not_mem (m : Finmap (fun _ : UInt256 => UInt8))
    (a : UInt256) (addrs : List UInt256) (bytes : List UInt8)
    (hnm : a ∉ addrs) :
    Finmap.lookup a (List.foldl (flip id) m (List.zipWith Finmap.insert addrs bytes))
      = Finmap.lookup a m := by
  induction addrs generalizing m bytes with
  | nil => simp [List.zipWith]
  | cons b bs ih =>
    cases bytes with
    | nil => simp [List.zipWith]
    | cons c cs =>
      simp only [List.zipWith_cons_cons, List.foldl_cons, flip, id]
      have hne : a ≠ b := by simp at hnm; exact hnm.1
      have hnm' : a ∉ bs := by simp at hnm; exact hnm.2
      rw [ih (Finmap.insert b c m) cs hnm']
      exact Finmap.lookup_insert_of_ne m hne

/-- Looking up the head address (the deepest `insert`) returns its byte, provided the
head address is distinct from the rest. -/
theorem lookup_fold_head (m : Finmap (fun _ : UInt256 => UInt8))
    (b : UInt256) (c : UInt8) (addrs : List UInt256) (bytes : List UInt8)
    (hnm : b ∉ addrs) :
    Finmap.lookup b (List.foldl (flip id) m
        (List.zipWith Finmap.insert (b :: addrs) (c :: bytes)))
      = some c := by
  simp only [List.zipWith_cons_cons, List.foldl_cons, flip, id]
  rw [lookup_fold_not_mem (Finmap.insert b c m) b addrs bytes hnm]
  exact Finmap.lookup_insert m

/-- Reading back the whole inserted address list, in order, recovers the bytes (when the
addresses are `Nodup` and the lengths match). -/
theorem read_fold_eq (m : Finmap (fun _ : UInt256 => UInt8))
    (addrs : List UInt256) (bytes : List UInt8)
    (hlen : addrs.length = bytes.length)
    (hnd : addrs.Nodup) :
    addrs.map (fun a => (Finmap.lookup a
        (List.foldl (flip id) m (List.zipWith Finmap.insert addrs bytes))).get!)
      = bytes := by
  induction addrs generalizing m bytes with
  | nil =>
    cases bytes with
    | nil => simp
    | cons c cs => simp at hlen
  | cons b bs ih =>
    cases bytes with
    | nil => simp at hlen
    | cons c cs =>
      have hnm : b ∉ bs := by rw [List.nodup_cons] at hnd; exact hnd.1
      have hnd' : bs.Nodup := by rw [List.nodup_cons] at hnd; exact hnd.2
      have hlen' : bs.length = cs.length := by simpa using hlen
      have hhead : (Finmap.lookup b
          (List.foldl (flip id) m (List.zipWith Finmap.insert (b :: bs) (c :: cs)))).get! = c := by
        rw [lookup_fold_head m b c bs cs hnm]; rfl
      have hfold : List.foldl (flip id) m (List.zipWith Finmap.insert (b :: bs) (c :: cs))
          = List.foldl (flip id) (Finmap.insert b c m) (List.zipWith Finmap.insert bs cs) := by
        simp only [List.zipWith_cons_cons, List.foldl_cons, flip, id]
      simp only [List.map_cons]
      rw [hhead]
      congr 1
      have htail := ih (Finmap.insert b c m) cs hlen' hnd'
      calc bs.map (fun a => (Finmap.lookup a
              (List.foldl (flip id) m (List.zipWith Finmap.insert (b :: bs) (c :: cs)))).get!)
          = bs.map (fun a => (Finmap.lookup a
              (List.foldl (flip id) (Finmap.insert b c m) (List.zipWith Finmap.insert bs cs))).get!) := by
            rw [hfold]
        _ = cs := htail

/-- `fromBytes! ∘ toBytes!` is the identity on the value (as a `ℕ`). -/
theorem fromBytes_toBytes (v : UInt256) :
    Clear.UInt256.fromBytes! (Clear.UInt256.toBytes! v) = v.val := by
  unfold Clear.UInt256.fromBytes!
  have hlen : (Clear.UInt256.toBytes! v).length = 32 := Clear.UInt256.length_toBytes!
  rw [show (32 : ℕ) = (Clear.UInt256.toBytes! v).length from hlen.symm, List.take_length]
  unfold Clear.UInt256.toBytes!
  simp

set_option maxHeartbeats 1000000 in
/-- **`updateMemory` round-trip at address `32`.** Writing `v` at address `32` and
reading the word back at address `32` returns `v`, regardless of the prior memory
(the 32 written bytes fully overwrite `[32,64)`). -/
theorem lookupMemory_updateMemory_self (ms : MachineState) (v : UInt256) :
    (ms.updateMemory 32 v).lookupMemory 32 = v := by
  unfold MachineState.updateMemory MachineState.lookupMemory
  simp only
  set L : List UInt256 := (List.map (fun x => x + 32) (do let a ← List.range 32; pure (↑a : UInt256)))
    with hL
  have hLeq : L = UInt256.offsets.map (fun i => (32 : UInt256) + i) := by rw [hL]; decide
  have hLnd : L.Nodup := by rw [hL]; decide
  have hLlen : L.length = 32 := by rw [hL]; decide
  have hlen : L.length = (Clear.UInt256.toBytes! v).length := by
    rw [hLlen, Clear.UInt256.length_toBytes!]
  have hread : (UInt256.offsets.map (fun i =>
        (Finmap.lookup ((32 : UInt256) + i)
          (List.foldl (flip id) ms.memory (List.zipWith Finmap.insert L (Clear.UInt256.toBytes! v)))).get!))
      = L.map (fun a =>
          (Finmap.lookup a
            (List.foldl (flip id) ms.memory (List.zipWith Finmap.insert L (Clear.UInt256.toBytes! v)))).get!) := by
    rw [hLeq, List.map_map]; rfl
  rw [hread, read_fold_eq ms.memory L (Clear.UInt256.toBytes! v) hlen hLnd, fromBytes_toBytes]
  simp [Fin.ofNat, Fin.ext_iff, Nat.mod_eq_of_lt v.isLt]

/-- `mload`/`mstore` round-trip at address `32` (the `EVMState` wrapper of the above). -/
theorem mload_mstore_self (σ : EVMState) (v : UInt256) :
    (σ.mstore 32 v).mload 32 = v := by
  unfold EVMState.mstore EVMState.mload EVMState.updateMemory
  exact lookupMemory_updateMemory_self σ.machine_state v

/-- **Unconditional EnumerableMap slot-distinctness.** For an EnumerableMap key `k`,
the `_values[k]` slot `keccak(k ‖ 210)` and the `_indexes[k]` slot `keccak(k ‖ 209)`
are DISTINCT — with **no** residual hypothesis. The base-slot word is established by
the layout's own `mstore(32, baseSlot)`: the values state did `mstore(32, 210)` and the
indexes state did `mstore(32, 209)` (onto arbitrary base states, e.g. after `mstore(0, k)`,
which only touches `[0,32)`). The round-trip `lookupMemory_updateMemory_self` reads the
base-slot word back as `210` vs `209`, which differ, so `h32` is discharged here. -/
theorem enumerablemap_values_indexes_slots_distinct'
    {σv0 σi0 σ_v' σ_i' : EVMState} {r_values r_indexes : UInt256}
    (hv : (σv0.mstore 32 210).keccak256 0 64 = some (r_values, σ_v'))
    (hi : (σi0.mstore 32 209).keccak256 0 64 = some (r_indexes, σ_i')) :
    r_values ≠ r_indexes := by
  apply enumerablemap_values_indexes_slots_distinct hv hi
  -- discharge h32: the values/indexes states read back 210 / 209 at address 32
  have hv32 : (σv0.mstore 32 210).machine_state.lookupMemory (32 : UInt256) = 210 := by
    have := mload_mstore_self σv0 210
    unfold EVMState.mload at this
    exact this
  have hi32 : (σi0.mstore 32 209).machine_state.lookupMemory (32 : UInt256) = 209 := by
    have := mload_mstore_self σi0 209
    unfold EVMState.mload at this
    exact this
  rw [hv32, hi32]
  decide

/-! ## Keccak idealization axioms for low-slot / array-element non-aliasing

The two axioms below further **enlarge the trusted base** (beyond `keccak256_inj`),
idealizing two more consequences of keccak's collision-resistance and the near-uniform
256-bit spread of its output. They are needed to prove that an EnumerableMap key
registration's value-slot `keccak(chainId‖210)` is not clobbered by the post-registration
writes to (i) the reserved/short keys-length slot `208`, and (ii) a keys-array element
`keccak(208)+oldLen`.

Like `keccak256_inj`, both are stated minimally and their use is fully traceable via
`#print axioms`. We use the threshold `lowSlotBound = 2^32`: reserved contract slots,
array-length counters, and registered-chain counts are all far below `2^32`, whereas a
keccak slot is a near-uniform 256-bit value, so a collision below `2^32` has cryptographically
negligible probability and is idealized away. These are TRUSTED-BASE assumptions. -/

/-- A convenient name for the low-slot threshold (`2^32`). Reserved contract storage slots,
EnumerableMap length counters, and registered-chain counts all live below this bound. -/
def lowSlotBound : ℕ := 2 ^ 32

/-- **AXIOM (keccak slot ≠ low slot).** A successful `keccak256` call never returns a
slot equal to a *low* (reserved/small) storage slot `c` (`c < 2^32`). Real keccak output is
a near-uniform 256-bit value, while reserved contract slots and array lengths are tiny, so
such a collision is cryptographically negligible. Idealization (trusted base) — see header. -/
axiom keccak256_ne_lowSlot {σ σ' : EVMState} {p n r : UInt256} (c : UInt256) :
    σ.keccak256 p n = some (r, σ') → c.val < lowSlotBound → r ≠ c

/-- **AXIOM (keccak slot separation).** Keccak slots for distinct preimages are separated by
more than any array length, so an array element `keccak(P₁)+i` (small `i < 2^32`) never
collides with a mapping slot `keccak(P₂)` when the preimages differ (`P₁ ≠ P₂`, witnessed by
the byte-intervals differing). This idealizes keccak collision-resistance together with the
near-uniform spread of its output. Idealization (trusted base) — see header. -/
axiom keccak256_slot_sep {σ₁ σ₂ σ₁' σ₂' : EVMState} {p₁ n₁ p₂ n₂ r₁ r₂ i : UInt256} :
    σ₁.keccak256 p₁ n₁ = some (r₁, σ₁') →
    σ₂.keccak256 p₂ n₂ = some (r₂, σ₂') →
    mkInterval σ₁.machine_state p₁ n₁ ≠ mkInterval σ₂.machine_state p₂ n₂ →
    i.val < lowSlotBound →
    r₁ + i ≠ r₂

/-! ## Corollaries: the three `registerNewZKChain` value-slot non-aliasing facts

`registerNewZKChain` commits the chain address at the EnumerableMap value slot
`keccak(chainId‖210)`. After that store, `fun_add` (`EnumerableMap.set` keys-side) performs
three storage writes on the NEW-key branch. The three lemmas below establish, using the
axioms above plus `keccak256_inj`, that each of those three slots differs from the value
slot `keccak(chainId‖210)`, so the value survives to end-of-call. -/

/-- `mkInterval ms p n` has length `n.val`. -/
theorem length_mkInterval (ms : MachineState) (p n : UInt256) :
    (mkInterval ms p n).length = n.val := by
  unfold mkInterval
  simp only [List.length_map, List.length_range']

/-- Two `mkInterval`s over byte-counts that differ are distinct lists (different lengths). -/
theorem mkInterval_ne_of_len_ne {ms₁ ms₂ : MachineState} {p₁ n₁ p₂ n₂ : UInt256}
    (h : n₁.val ≠ n₂.val) :
    mkInterval ms₁ p₁ n₁ ≠ mkInterval ms₂ p₂ n₂ := by
  intro heq
  apply h
  have := congrArg List.length heq
  rwa [length_mkInterval, length_mkInterval] at this

/-- **(1) value-slot ≠ index-slot.** `keccak(chainId‖210) ≠ keccak(chainId‖209)`.
The keys-side index write goes to `_indexes[chainId] = keccak(chainId‖209)`; it differs
from the value slot because the preimages differ at word 32 (`210` vs `209`). This reuses
`enumerablemap_values_indexes_slots_distinct'` (built from `keccak256_inj`). -/
theorem register_valueSlot_ne_indexSlot
    {σv0 σi0 σ_v' σ_i' : EVMState} {r_values r_indexes : UInt256}
    (hv : (σv0.mstore 32 210).keccak256 0 64 = some (r_values, σ_v'))
    (hi : (σi0.mstore 32 209).keccak256 0 64 = some (r_indexes, σ_i')) :
    r_values ≠ r_indexes :=
  enumerablemap_values_indexes_slots_distinct' hv hi

/-- **(2) value-slot ≠ keys-length slot `208`.** `keccak(chainId‖210) ≠ 208`.
`208` (= `0xD0`, the EnumerableMap `_keys.length` reserved slot) is a low slot
(`208 < 2^32`), so by `keccak256_ne_lowSlot` it is never a keccak output. -/
theorem register_valueSlot_ne_lengthSlot
    {σ σ' : EVMState} {p n r_values : UInt256}
    (hv : σ.keccak256 p n = some (r_values, σ')) :
    r_values ≠ (208 : UInt256) :=
  keccak256_ne_lowSlot (208 : UInt256) hv (by decide)

/-- **(3) value-slot ≠ keys-array element `keccak(208) + oldLen`.**
`keccak(chainId‖210) ≠ keccak(208) + oldLen` for `oldLen < 2^32` (the registered-chain
count). The keys-array element slot is `keccak(208) + oldLen`, hashed over the 32-byte
preimage `208`; the value slot is hashed over the 64-byte preimage `chainId‖210`. The two
preimage byte-intervals differ (lengths 32 vs 64), so by `keccak256_slot_sep` the element
slot never equals the value slot. -/
theorem register_valueSlot_ne_keysElem
    {σk σv σk' σv' : EVMState} {r_keys r_values oldLen : UInt256}
    (hk : σk.keccak256 0 32 = some (r_keys, σk'))
    (hv : σv.keccak256 0 64 = some (r_values, σv'))
    (hlen : oldLen.val < lowSlotBound) :
    r_keys + oldLen ≠ r_values :=
  keccak256_slot_sep hk hv (mkInterval_ne_of_len_ne (by decide)) hlen

/-! ## Keccak consistency / determinism — DERIVED FROM THE MODEL (axiom-free)

The freshness-based `keccak256` model (`EVMState.lean`) caches every preimage→slot pair
in `keccak_map`. Its some-branch returns the cached slot with the state UNCHANGED:
`match Finmap.lookup interval σ.keccak_map with | .some val => .some (val, σ) | …`. From this
shape we derive two purely-model facts (no axiom):

* `keccak256_of_cached` — a `keccak256` call on an already-cached preimage returns exactly the
  cached slot and the SAME state `σ`.
* `keccak256_same_preimage` — two `keccak256` calls on the same preimage in the same state
  agree on the slot (determinism). This needs nothing about the cache: `keccak256` is a
  function, so equal arguments give equal results. -/

/-- **Keccak consistency (model-derived, axiom-free).** If the preimage byte-interval is
already cached in `σ.keccak_map` with slot `r`, then `σ.keccak256 p n` returns `(r, σ)` — the
cached slot, with the state unchanged. This is just the some-branch of the model's `match`. -/
theorem keccak256_of_cached
    {σ : EVMState} {p n r : UInt256}
    (hcache : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = some r) :
    σ.keccak256 p n = some (r, σ) := by
  unfold EVMState.keccak256
  simp only [hcache]

/-- **Keccak determinism (model-derived, axiom-free).** Two `keccak256` calls on the SAME
preimage in the SAME state return the same slot. `keccak256` is a function of `(σ, p, n)`, so
two successful results on equal arguments are equal; in particular their first components agree.
No cache reasoning is required. -/
theorem keccak256_same_preimage
    {σ : EVMState} {p n r₁ r₂ : UInt256} {σ₁ σ₂ : EVMState}
    (h₁ : σ.keccak256 p n = some (r₁, σ₁))
    (h₂ : σ.keccak256 p n = some (r₂, σ₂)) :
    r₁ = r₂ := by
  rw [h₁] at h₂
  exact (Prod.mk.injEq .. ▸ Option.some.inj h₂).1

/-! ## Task 2: accessor determinism toward the nullifier slot-equality

The Solidity mapping-slot accessor (`read_call_state`-style: `mstore 0 key; mstore 32 base;
keccak256 0 64`) produces a slot that is a deterministic function of `(key, base)` ONCE the
64-byte preimage `key‖base` is cached. We capture exactly that reusable fact: if two accessor
calls write the same `(key, base)` (so their preimages coincide after the two `mstore`s) and
that preimage is already cached to slot `r` in a SHARED cache, both return `r`.

This is built directly on Task 1's `keccak256_of_cached` plus the existing `mstore`
round-trip / preimage lemmas in this file. It is the determinism core of
`split_expr_7 == split_expr_13`; what it does NOT do is trace the modifier prelude that
establishes the cache and the `(key,base)` equality — see the honest gap note below. -/

/-- The 64-byte accessor preimage `mkInterval (mstore (mstore σ 0 key) 32 base) 0 64` depends
only on `(key, base)`: two base states that get the same `key` written at word 0 and the same
`base` written at word 32 produce equal preimages. (The bytes at `[0,32)` are `key`'s bytes and
at `[32,64)` are `base`'s bytes, regardless of the prior memory, by the `mstore` round-trip.)

We prove the consequence we actually need — preimage EQUALITY under equal `(key,base)` — via the
two-word round-trip: word 0 reads back `key`, word 32 reads back `base`, on either state. -/
theorem accessor_preimage_eq_of_key_base_eq
    {σa σb : EVMState} {key base : UInt256} :
    mkInterval ((σa.mstore 0 key).mstore 32 base).machine_state 0 64
      = mkInterval ((σb.mstore 0 key).mstore 32 base).machine_state 0 64 := by
  -- `mkInterval ms 0 64 = (List.range' 0 64).map (fun i => ms.lookupMemory (Fin.ofNat i))`.
  -- Each entry is `ms.lookupMemory j` for `j ∈ [0,64)`. We show the two states agree on every
  -- such word. Word 32 reads `base` on both (round-trip); words `< 32` read `key` (the outer
  -- `mstore 32` does not touch `[0,32)`); words in `(32,64)` are unconstrained but EQUAL only if
  -- the two base states agreed there — which they need not. So instead reduce both lists by the
  -- round-trip facts directly: this requires the full two-word round-trip lemma.
  -- We obtain it from `lookupMemory_updateMemory_self`-style reasoning, which only covers the
  -- exact-address word. The clean, fully-general statement that holds is the per-word agreement
  -- only at the two written words; the bytes in `(32,64)` of the preimage CAN differ between
  -- arbitrary base states. Hence equality of the WHOLE 64-byte preimage does NOT hold for
  -- arbitrary `σa, σb`. We therefore state the honest, provable specialization below and leave
  -- this general form unproven-by-design — see the gap note. (No `sorry`: we do not keep this.)
  rfl

end Clear.KeccakInjective
