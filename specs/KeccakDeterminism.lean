import Clear.EVMState

/-!
# Keccak accessor determinism (MODEL-DERIVED, AXIOM-FREE)

The Solidity mapping-slot accessor (`mstore 0 key; mstore 32 base; keccak256 0 64`)
produces a slot that is a deterministic function of `(key, base)` — *provided* the
"junk window" of the 64-byte hash interval agrees between runs. In Clear's model,
`mkInterval ms 0 64` is the list `[lookupMemory 0, …, lookupMemory 63]`, and
`lookupMemory j` reads the 32 bytes at `[j, j+32)`; so the interval depends on
memory bytes `[0, 95)`: the two `mstore`s determine bytes `[0, 64)`, while bytes
`[64, 95)` leak in from the pre-existing memory. The unconditional
"preimage depends only on `(key, base)`" is therefore FALSE in the model. The
honest, provable form is *frame-conditioned*: if two accessor runs write the same
`(key, base)` AND their base states agree on bytes `[64, 95)`, the preimages
coincide (`accessor_interval_eq`). Combined with the cache/monotonicity lemmas
this yields full **accessor-chain determinism** (`accessor_chain_deterministic`):
re-running the 3-level nested accessor chain (the
`isWithdrawalFinalized[chainId][batch][index]` slot computation) returns the same
three slots, provided nothing in between touched bytes `[64, 95)` or dropped
keccak-cache entries, and the first run's post-state is hash-collision-free.

This is the determinism core of `split_expr_7 == split_expr_13` in the
L1Nullifier replay chain — the "slot CHECKED = slot SET" linkage flagged as
future work in `no_replay_user.lean`, discharged there via the closed forms of
the generated `mapping_index_access_…` helpers.

Everything here is derived from the model: **no axioms** beyond the standard
kernel ones (verify with `#print axioms accessor_chain_deterministic`).
-/

namespace Clear.KeccakDeterminism

open Clear EVMState

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-! ## keccak256 post-state facts (some-branch) -/

/-- `keccak256` (some-branch) leaves the machine state (memory) unchanged. -/
theorem keccak256_machine_state
    {σ : EVMState} {p n : UInt256} {pr : UInt256 × EVMState}
    (h : σ.keccak256 p n = some pr) :
    pr.2.machine_state = σ.machine_state := by
  obtain ⟨r, σ'⟩ := pr
  unfold EVMState.keccak256 at h
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some val =>
    simp only [hl] at h
    obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    rw [← h2]
  | none =>
    simp only [hl] at h
    cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
    | mk used unused =>
      cases unused with
      | nil => simp only [hpart] at h
      | cons hd tl =>
        simp only [hpart] at h
        obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rw [← h2]

/-- `keccak256` (some-branch) preserves the `hash_collision` flag. -/
theorem keccak256_hash_collision
    {σ : EVMState} {p n : UInt256} {pr : UInt256 × EVMState}
    (h : σ.keccak256 p n = some pr) :
    pr.2.hash_collision = σ.hash_collision := by
  obtain ⟨r, σ'⟩ := pr
  unfold EVMState.keccak256 at h
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some val =>
    simp only [hl] at h
    obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    rw [← h2]
  | none =>
    simp only [hl] at h
    cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
    | mk used unused =>
      cases unused with
      | nil => simp only [hpart] at h
      | cons hd tl =>
        simp only [hpart] at h
        obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rw [← h2]

/-- `keccak256` (some-branch) preserves existing cache entries: the map only
grows, and only by a key that was previously absent. -/
theorem keccak256_lookup_mono
    {σ : EVMState} {p n : UInt256} {pr : UInt256 × EVMState}
    {I : List UInt256} {w : UInt256}
    (h : σ.keccak256 p n = some pr)
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I pr.2.keccak_map = some w := by
  obtain ⟨r, σ'⟩ := pr
  unfold EVMState.keccak256 at h
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some val =>
    simp only [hl] at h
    obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    rw [← h2]; exact hI
  | none =>
    simp only [hl] at h
    cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
    | mk used unused =>
      cases unused with
      | nil => simp only [hpart] at h
      | cons hd tl =>
        simp only [hpart] at h
        obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rw [← h2]
        have hne : I ≠ mkInterval σ.machine_state p n := by
          intro he; rw [he, hl] at hI; exact Option.noConfusion hI
        rw [show ({σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p n) hd,
                          keccak_range := tl,
                          used_range := {hd} ∪ σ.used_range} : EVMState).keccak_map
              = σ.keccak_map.insert (mkInterval σ.machine_state p n) hd from rfl]
        rw [Finmap.lookup_insert_of_ne _ hne]
        exact hI

/-- After a successful `keccak256`, the hashed preimage is cached to the returned
slot in the post-state. -/
theorem keccak256_caches
    {σ : EVMState} {p n : UInt256} {pr : UInt256 × EVMState}
    (h : σ.keccak256 p n = some pr) :
    Finmap.lookup (mkInterval σ.machine_state p n) pr.2.keccak_map = some pr.1 := by
  obtain ⟨r, σ'⟩ := pr
  unfold EVMState.keccak256 at h
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some val =>
    simp only [hl] at h
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    rw [← h2, hl, h1]
  | none =>
    simp only [hl] at h
    cases hpart : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with
    | mk used unused =>
      cases unused with
      | nil => simp only [hpart] at h
      | cons hd tl =>
        simp only [hpart] at h
        obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rw [← h2, ← h1]
        exact Finmap.lookup_insert _

/-- Cached-hit form of `keccak256` (some-branch of the model's `match`). -/
theorem keccak256_of_cached'
    {σ : EVMState} {p n r : UInt256}
    (hcache : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = some r) :
    σ.keccak256 p n = some (r, σ) := by
  unfold EVMState.keccak256
  simp only [hcache]

/-! ## `keccakOut`: total-function view of the keccak PRIMOP -/

/-- Total-function view of the `keccak256` PRIMOP result (`EVMKeccak256'`): the
returned slot and post-state, with the hash-collision fallback (`none`) inlined
as `(0, σ.addHashCollision)`. -/
def keccakOut (σ : EVMState) (p n : UInt256) : UInt256 × EVMState :=
  match σ.keccak256 p n with
  | some pr => pr
  | none    => (0, σ.addHashCollision)

/-- If the post-state of `keccakOut` is collision-free, the call took the
some-branch: `keccak256` genuinely succeeded with exactly that result. -/
theorem keccakOut_some_of_clean
    {σ : EVMState} {p n : UInt256}
    (h : (keccakOut σ p n).2.hash_collision = false) :
    σ.keccak256 p n = some (keccakOut σ p n) := by
  rcases hk : σ.keccak256 p n with _ | pr
  · exfalso
    simp only [keccakOut, hk] at h
    simp [EVMState.addHashCollision] at h
  · simp only [keccakOut, hk]

/-- `keccakOut` preserves existing cache entries in every branch. -/
theorem keccakOut_lookup_mono
    {σ : EVMState} {p n : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (keccakOut σ p n).2.keccak_map = some w := by
  rcases hk : σ.keccak256 p n with _ | pr
  · simp only [keccakOut, hk]
    exact hI
  · simp only [keccakOut, hk]
    exact keccak256_lookup_mono hk hI

/-- `keccakOut` leaves the machine state (memory) unchanged in every branch. -/
theorem keccakOut_machine_state (σ : EVMState) (p n : UInt256) :
    (keccakOut σ p n).2.machine_state = σ.machine_state := by
  rcases hk : σ.keccak256 p n with _ | pr
  · simp only [keccakOut, hk]
    rfl
  · simp only [keccakOut, hk]
    exact keccak256_machine_state hk

/-- A collision-free `keccakOut` post-state forces a collision-free input state. -/
theorem keccakOut_clean_backward
    {σ : EVMState} {p n : UInt256}
    (h : (keccakOut σ p n).2.hash_collision = false) :
    σ.hash_collision = false := by
  have hs := keccakOut_some_of_clean h
  rw [keccak256_hash_collision hs] at h
  exact h

/-- A collision-free successful `keccakOut` caches its preimage to the returned
slot. -/
theorem keccakOut_caches_of_clean
    {σ : EVMState} {p n : UInt256}
    (h : (keccakOut σ p n).2.hash_collision = false) :
    Finmap.lookup (mkInterval σ.machine_state p n) (keccakOut σ p n).2.keccak_map
      = some (keccakOut σ p n).1 :=
  keccak256_caches (keccakOut_some_of_clean h)

/-- Cached-hit form: if the preimage is already cached, `keccakOut` returns the
cached slot with the state unchanged. -/
theorem keccakOut_of_cached
    {σ : EVMState} {p n r : UInt256}
    (hcache : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = some r) :
    keccakOut σ p n = (r, σ) := by
  unfold keccakOut
  rw [keccak256_of_cached' hcache]

/-! ## Byte-level contract of `updateMemory`

`updateMemory a v` folds 32 byte-inserts of `toBytes! v` at addresses
`a+0 … a+31`. We canonicalize that address list to
`(List.range 32).map (fun k => ↑k + a)` and derive the two byte-level facts we
need: reading OUTSIDE the window is unchanged, and reading the `k`-th window
address returns the `k`-th byte of `v` (a pure function of `(v, k)`).

The fold helpers below are self-contained (the analogous helpers in
`specs/KeccakInjective.lean` are not imported, to keep this file free of even
the *presence* of the trusted-base axioms). -/

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

/-- Looking up the `k`-th folded address returns the `k`-th byte (`Nodup` addrs,
matching lengths). -/
theorem lookup_fold_at (m : Finmap (fun _ : UInt256 => UInt8))
    (addrs : List UInt256) (bytes : List UInt8) (k : ℕ)
    (hk : k < addrs.length)
    (hlen : addrs.length = bytes.length) (hnd : addrs.Nodup) :
    Finmap.lookup (addrs.get ⟨k, hk⟩)
        (List.foldl (flip id) m (List.zipWith Finmap.insert addrs bytes))
      = bytes.get? k := by
  induction addrs generalizing m bytes k with
  | nil => simp at hk
  | cons b bs ih =>
    cases bytes with
    | nil => simp at hlen
    | cons c cs =>
      rw [List.nodup_cons] at hnd
      cases k with
      | zero =>
        simp only [List.get, List.get?]
        simp only [List.zipWith_cons_cons, List.foldl_cons, flip, id]
        rw [lookup_fold_not_mem (Finmap.insert b c m) b bs cs hnd.1]
        exact Finmap.lookup_insert m
      | succ k' =>
        have hk' : k' < bs.length := by simpa using hk
        have hlen' : bs.length = cs.length := by simpa using hlen
        simp only [List.get, List.get?]
        simp only [List.zipWith_cons_cons, List.foldl_cons, flip, id]
        exact ih (Finmap.insert b c m) cs k' hk' hlen' hnd.2

/-- The canonical form of the 32 byte-addresses written by `updateMemory a _`. -/
def window (a : UInt256) : List UInt256 :=
  (List.range 32).map (fun k : ℕ => ((↑k : UInt256) + a))

/-- `updateMemory`'s memory is the byte-fold over `window a`. -/
theorem updateMemory_memory (m : MachineState) (a v : UInt256) :
    (m.updateMemory a v).memory
      = List.foldl (flip id) m.memory
          (List.zipWith Finmap.insert (window a) (Clear.UInt256.toBytes! v)) := by
  unfold MachineState.updateMemory
  simp only
  have haddr : (List.map (fun x => x + a)
        (do let k ← List.range 32; pure ((↑k : UInt256)))) = window a := by
    unfold window
    have hco : (do let k ← List.range 32; pure ((↑k : UInt256)))
        = (List.range 32).map (fun k : ℕ => ((↑k : UInt256))) := by decide
    rw [hco, List.map_map]
    rfl
  rw [haddr]

/-- Reading outside the written window leaves the byte unchanged. -/
theorem lookup_updateMemory_outside (m : MachineState) (a v : UInt256) (i : UInt256)
    (h : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + a) :
    Finmap.lookup i (m.updateMemory a v).memory = Finmap.lookup i m.memory := by
  rw [updateMemory_memory]
  apply lookup_fold_not_mem
  intro hmem
  unfold window at hmem
  rw [List.mem_map] at hmem
  obtain ⟨k, hk, hki⟩ := hmem
  rw [List.mem_range] at hk
  exact h k hk hki.symm

/-- Reading the `k`-th window address returns the `k`-th byte of `v` — a pure
function of `(v, k)`, independent of the prior memory. -/
theorem lookup_updateMemory_at (m : MachineState) (a v : UInt256) (k : ℕ) (hk : k < 32)
    (hnd : (window a).Nodup) :
    Finmap.lookup ((↑k : UInt256) + a) (m.updateMemory a v).memory
      = (Clear.UInt256.toBytes! v).get? k := by
  rw [updateMemory_memory]
  have hklen : k < (window a).length := by
    unfold window; simpa using hk
  have hget? : (window a).get? k = some ((↑k : UInt256) + a) := by
    unfold window
    rw [List.get?_map, List.get?_range hk]
    rfl
  have hget : (window a).get ⟨k, hklen⟩ = (↑k : UInt256) + a := by
    have h1 : (window a).get? k = some ((window a).get ⟨k, hklen⟩) := List.get?_eq_get hklen
    rw [hget?] at h1
    exact (Option.some.inj h1).symm
  have hlen : (window a).length = (Clear.UInt256.toBytes! v).length := by
    unfold window
    simp [Clear.UInt256.length_toBytes!]
  rw [← hget]
  exact lookup_fold_at m.memory (window a) (Clear.UInt256.toBytes! v) k hklen hlen hnd

/-- `window 0` has no duplicates. -/
theorem window_zero_nodup : (window (0 : UInt256)).Nodup := by decide

/-- `window 32` has no duplicates. -/
theorem window_32_nodup : (window (32 : UInt256)).Nodup := by decide

private lemma uint256_size_eq : UInt256.size = 2 ^ 256 := by norm_num

private lemma val_coe_add (k : ℕ) (a : UInt256) (hk : k < 32) (ha : a.val + 32 ≤ 2 ^ 256) :
    (((↑k : UInt256) + a)).val = k + a.val := by
  have hs := uint256_size_eq
  have hks : k < UInt256.size := by omega
  have hkv : ((↑k : UInt256)).val = k := Fin.val_cast_of_lt hks
  have h1 : (((↑k : UInt256) + a)).val
      = (((↑k : UInt256)).val + a.val) % UInt256.size := rfl
  rw [h1, hkv]
  exact Nat.mod_eq_of_lt (by omega)

private lemma val_32 : ((32 : UInt256)).val = 32 := by decide

private lemma val_0 : ((0 : UInt256)).val = 0 := by decide

/-! ## Frame-conditioned accessor preimage equality -/

/-- Byte agreement for the accessor's double `mstore`: at every byte address
`i.val ≤ 94`, two states that receive the same `key` at word 0 and the same
`base` at word 32, and agree on the junk window `[64, 95)`, have equal bytes. -/
theorem byte_double_mstore_eq
    {σ₁ σ₂ : EVMState} {key base : UInt256} {i : UInt256}
    (hi : i.val ≤ 94)
    (hframe : 64 ≤ i.val →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory) :
    Finmap.lookup i ((σ₁.mstore 0 key).mstore 32 base).machine_state.memory
      = Finmap.lookup i ((σ₂.mstore 0 key).mstore 32 base).machine_state.memory := by
  have hms : ∀ σ : EVMState,
      ((σ.mstore 0 key).mstore 32 base).machine_state
        = (σ.machine_state.updateMemory 0 key).updateMemory 32 base := fun _ => rfl
  rw [hms σ₁, hms σ₂]
  rcases Nat.lt_or_ge i.val 32 with h32 | h32
  · -- window-0 byte: not in window 32; determined by `key` on both sides
    have hout32 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 32 := by
      intro k hk he
      have : i.val = k + 32 := by
        rw [he, val_coe_add k 32 hk (by rw [val_32]; norm_num)]
        rw [val_32]
      omega
    rw [lookup_updateMemory_outside _ 32 base i hout32,
        lookup_updateMemory_outside _ 32 base i hout32]
    have hin : i = (↑(i.val) : UInt256) + 0 := by
      rw [add_zero, Fin.cast_val_eq_self]
    rw [hin,
        lookup_updateMemory_at _ 0 key i.val h32 window_zero_nodup,
        lookup_updateMemory_at _ 0 key i.val h32 window_zero_nodup]
  · rcases Nat.lt_or_ge i.val 64 with h64 | h64
    · -- window-32 byte: determined by `base` on both sides
      have hin : i = (↑(i.val - 32) : UInt256) + 32 := by
        apply Fin.ext
        rw [val_coe_add (i.val - 32) 32 (by omega) (by rw [val_32]; norm_num), val_32]
        omega
      rw [hin,
          lookup_updateMemory_at _ 32 base (i.val - 32) (by omega) window_32_nodup,
          lookup_updateMemory_at _ 32 base (i.val - 32) (by omega) window_32_nodup]
    · -- junk-window byte: outside both windows on both sides → frame hypothesis
      have hout32 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 32 := by
        intro k hk he
        have : i.val = k + 32 := by
          rw [he, val_coe_add k 32 hk (by rw [val_32]; norm_num)]
          rw [val_32]
        omega
      have hout0 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 0 := by
        intro k hk he
        have : i.val = k + 0 := by
          rw [he, val_coe_add k 0 hk (by rw [val_0]; norm_num)]
          rw [val_0]
        omega
      rw [lookup_updateMemory_outside _ 32 base i hout32,
          lookup_updateMemory_outside _ 0 key i hout0,
          lookup_updateMemory_outside _ 32 base i hout32,
          lookup_updateMemory_outside _ 0 key i hout0]
      exact hframe h64

/-- Word agreement: every word `j < 64` of the double-`mstore`d states agrees
(each such word reads bytes `[j, j+32) ⊆ [0, 95)`). -/
theorem lookupMemory_double_mstore_eq
    {σ₁ σ₂ : EVMState} {key base : UInt256} {j : UInt256}
    (hj : j.val < 64)
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory) :
    ((σ₁.mstore 0 key).mstore 32 base).machine_state.lookupMemory j
      = ((σ₂.mstore 0 key).mstore 32 base).machine_state.lookupMemory j := by
  simp only [MachineState.lookupMemory]
  refine congrArg (fun l => ((Clear.UInt256.fromBytes! l : ℕ) : UInt256)) ?_
  have hoffs : UInt256.offsets = (List.range 32).map (fun k : ℕ => ((↑k : UInt256))) := by
    decide
  rw [hoffs, List.map_map, List.map_map]
  apply List.map_congr
  intro k hk
  rw [List.mem_range] at hk
  simp only [Function.comp]
  have hs := uint256_size_eq
  have hkv : ((↑k : UInt256)).val = k := Fin.val_cast_of_lt (by omega)
  have hjov : (j + (↑k : UInt256)).val = j.val + k := by
    have h1 : (j + (↑k : UInt256)).val = (j.val + ((↑k : UInt256)).val) % UInt256.size := rfl
    rw [h1, hkv]
    exact Nat.mod_eq_of_lt (by omega)
  have hle : (j + (↑k : UInt256)).val ≤ 94 := by omega
  have hbyte := byte_double_mstore_eq (σ₁ := σ₁) (σ₂ := σ₂) (key := key) (base := base)
      (i := j + (↑k : UInt256)) hle
      (fun h64 => hframe (j + (↑k : UInt256)) h64 hle)
  rw [hbyte]

/-- **Frame-conditioned accessor preimage equality** (the honest, provable form
of "the accessor preimage depends only on `(key, base)`"): two accessor runs
writing the same `(key, base)` from base states that agree on the junk window
`[64, 95)` produce **equal** 64-byte keccak intervals. -/
theorem accessor_interval_eq
    {σ₁ σ₂ : EVMState} {key base : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory) :
    mkInterval ((σ₁.mstore 0 key).mstore 32 base).machine_state 0 64
      = mkInterval ((σ₂.mstore 0 key).mstore 32 base).machine_state 0 64 := by
  unfold EVMState.mkInterval
  apply List.map_congr
  intro j hj
  rw [List.mem_map] at hj
  obtain ⟨j', hj', rfl⟩ := hj
  have h64 : ((64 : UInt256)).val = 64 := by decide
  have h0 : ((0 : UInt256)).val = 0 := by decide
  rw [h0, h64, List.mem_range'_1] at hj'
  have hj64 : j' < 64 := by omega
  have hs := uint256_size_eq
  have hjv : (Fin.ofNat j' : UInt256).val < 64 := by
    have hv : (Fin.ofNat j' : UInt256).val = j' % UInt256.size := rfl
    rw [hv, Nat.mod_eq_of_lt (by omega)]
    exact hj64
  exact lookupMemory_double_mstore_eq hjv hframe

/-! ## The accessor step and chain determinism -/

/-- One mapping-accessor step at the EVM level: write `key` at word 0, `base` at
word 32, hash the 64-byte scratch. Returns `(slot, post-evm)`. This is the exact
evm-effect of the generated `mapping_index_access_…` helpers (see the closed
forms in `no_replay_user.lean`). -/
def accOut (σ : EVMState) (key base : UInt256) : UInt256 × EVMState :=
  keccakOut ((σ.mstore 0 key).mstore 32 base) 0 64

/-- The keccak preimage interval of one accessor step. -/
def accInterval (σ : EVMState) (key base : UInt256) : List UInt256 :=
  mkInterval ((σ.mstore 0 key).mstore 32 base).machine_state 0 64

/-- `mstore` does not change the keccak cache. -/
theorem keccak_map_mstore (σ : EVMState) (a v : UInt256) :
    (σ.mstore a v).keccak_map = σ.keccak_map := rfl

/-- `mstore` does not change the collision flag. -/
theorem hash_collision_mstore (σ : EVMState) (a v : UInt256) :
    (σ.mstore a v).hash_collision = σ.hash_collision := rfl

/-- `accOut` preserves existing cache entries. -/
theorem accOut_lookup_mono
    {σ : EVMState} {key base : UInt256} {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (accOut σ key base).2.keccak_map = some w := by
  unfold accOut
  exact keccakOut_lookup_mono (by rw [keccak_map_mstore, keccak_map_mstore]; exact hI)

/-- A collision-free `accOut` post-state forces a collision-free input state. -/
theorem accOut_clean_backward
    {σ : EVMState} {key base : UInt256}
    (h : (accOut σ key base).2.hash_collision = false) :
    σ.hash_collision = false := by
  unfold accOut at h
  have := keccakOut_clean_backward h
  rw [hash_collision_mstore, hash_collision_mstore] at this
  exact this

/-- A collision-free successful `accOut` caches its preimage to the returned slot. -/
theorem accOut_caches_of_clean
    {σ : EVMState} {key base : UInt256}
    (h : (accOut σ key base).2.hash_collision = false) :
    Finmap.lookup (accInterval σ key base) (accOut σ key base).2.keccak_map
      = some (accOut σ key base).1 :=
  keccakOut_caches_of_clean h

/-- Cached-hit form: if the step's preimage is already cached to `r`, the step
returns `r` and the post-evm is just the double-`mstore`d input. -/
theorem accOut_of_cached
    {σ : EVMState} {key base r : UInt256}
    (hcache : Finmap.lookup (accInterval σ key base) σ.keccak_map = some r) :
    accOut σ key base = (r, (σ.mstore 0 key).mstore 32 base) := by
  unfold accOut
  unfold accInterval at hcache
  have hmap : ((σ.mstore 0 key).mstore 32 base).keccak_map = σ.keccak_map := rfl
  apply keccakOut_of_cached
  rw [hmap]
  exact hcache

/-- The junk window `[64, 95)` survives an accessor step (the two `mstore`s only
write `[0, 64)` and the keccak does not touch memory). -/
theorem accOut_junk_window
    {σ : EVMState} {key base : UInt256} {i : UInt256}
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (accOut σ key base).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  unfold accOut
  rw [keccakOut_machine_state]
  have hout32 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 32 := by
    intro k hk he
    have : i.val = k + 32 := by
      rw [he, val_coe_add k 32 hk (by rw [val_32]; norm_num)]
      rw [val_32]
    omega
  have hout0 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 0 := by
    intro k hk he
    have : i.val = k + 0 := by
      rw [he, val_coe_add k 0 hk (by rw [val_0]; norm_num)]
      rw [val_0]
    omega
  have hms : ((σ.mstore 0 key).mstore 32 base).machine_state
      = (σ.machine_state.updateMemory 0 key).updateMemory 32 base := rfl
  rw [hms, lookup_updateMemory_outside _ 32 base i hout32,
      lookup_updateMemory_outside _ 0 key i hout0]

/-- Frame-conditioned preimage equality, `accInterval` form. -/
theorem accInterval_eq
    {σ₁ σ₂ : EVMState} {key base : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory) :
    accInterval σ₁ key base = accInterval σ₂ key base :=
  accessor_interval_eq hframe

/-- **Accessor-chain determinism.** Running the 3-level nested mapping accessor
twice with the same keys `(k₁, k₂, k₃)` and base `b` returns the same three
slots, provided:
* the re-run's start state agrees with the first run's end state on the junk
  window `[64, 95)` (`hmem`),
* no keccak-cache entry present after the first run was dropped (`hmono`), and
* the first run's post-state is hash-collision-free (`hclean`).

The re-run then *hits the cache at every level* — no cleanliness assumption is
needed for the second run at all. This is the model-derived determinism core of
the L1Nullifier `split_expr_7 == split_expr_13` slot-equality. Axiom-free. -/
theorem accessor_chain_deterministic
    {σ₀ σmid : EVMState} {k₁ k₂ k₃ b : UInt256}
    {r₅ r₆ r₇ r₁₁ r₁₂ r₁₃ : UInt256} {e₅ e₆ e₇ e₁₁ e₁₂ e₁₃ : EVMState}
    (h₅ : accOut σ₀ k₁ b = (r₅, e₅))
    (h₆ : accOut e₅ k₂ r₅ = (r₆, e₆))
    (h₇ : accOut e₆ k₃ r₆ = (r₇, e₇))
    (hmem : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σmid.machine_state.memory
        = Finmap.lookup i e₇.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I e₇.keccak_map = some w → Finmap.lookup I σmid.keccak_map = some w)
    (h₁₁ : accOut σmid k₁ b = (r₁₁, e₁₁))
    (h₁₂ : accOut e₁₁ k₂ r₁₁ = (r₁₂, e₁₂))
    (h₁₃ : accOut e₁₂ k₃ r₁₂ = (r₁₃, e₁₃))
    (hclean : e₇.hash_collision = false) :
    r₁₁ = r₅ ∧ r₁₂ = r₆ ∧ r₁₃ = r₇ := by
  -- First-run cleanliness propagates backward through the chain.
  have hclean₆ : e₆.hash_collision = false := by
    have := accOut_clean_backward (σ := e₆) (key := k₃) (base := r₆)
      (by rw [h₇]; exact hclean)
    exact this
  have hclean₅ : e₅.hash_collision = false := by
    have := accOut_clean_backward (σ := e₅) (key := k₂) (base := r₅)
      (by rw [h₆]; exact hclean₆)
    exact this
  -- First-run cache facts (each level caches its preimage to its slot).
  have hc₅ : Finmap.lookup (accInterval σ₀ k₁ b) e₅.keccak_map = some r₅ := by
    have := accOut_caches_of_clean (σ := σ₀) (key := k₁) (base := b)
      (by rw [h₅]; exact hclean₅)
    rw [h₅] at this; exact this
  have hc₆ : Finmap.lookup (accInterval e₅ k₂ r₅) e₆.keccak_map = some r₆ := by
    have := accOut_caches_of_clean (σ := e₅) (key := k₂) (base := r₅)
      (by rw [h₆]; exact hclean₆)
    rw [h₆] at this; exact this
  have hc₇ : Finmap.lookup (accInterval e₆ k₃ r₆) e₇.keccak_map = some r₇ := by
    have := accOut_caches_of_clean (σ := e₆) (key := k₃) (base := r₆)
      (by rw [h₇]; exact hclean)
    rw [h₇] at this; exact this
  -- Those entries survive to the end of the first run…
  have hc₅₆ : Finmap.lookup (accInterval σ₀ k₁ b) e₆.keccak_map = some r₅ := by
    have := accOut_lookup_mono (σ := e₅) (key := k₂) (base := r₅) hc₅
    rw [h₆] at this; exact this
  have hc₅₇ : Finmap.lookup (accInterval σ₀ k₁ b) e₇.keccak_map = some r₅ := by
    have := accOut_lookup_mono (σ := e₆) (key := k₃) (base := r₆) hc₅₆
    rw [h₇] at this; exact this
  have hc₆₇ : Finmap.lookup (accInterval e₅ k₂ r₅) e₇.keccak_map = some r₆ := by
    have := accOut_lookup_mono (σ := e₆) (key := k₃) (base := r₆) hc₆
    rw [h₇] at this; exact this
  -- …and into the re-run's start state.
  have hm₅ := hmono _ _ hc₅₇
  have hm₆ := hmono _ _ hc₆₇
  have hm₇ := hmono _ _ hc₇
  -- Junk-window bookkeeping: e₅, e₆, e₇ (hence σmid) all agree with σ₀ on [64, 95).
  have hj₅ : ∀ i : UInt256, 64 ≤ i.val →
      Finmap.lookup i e₅.machine_state.memory = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi
    have := accOut_junk_window (σ := σ₀) (key := k₁) (base := b) (i := i) hi
    rw [h₅] at this; exact this
  have hj₆ : ∀ i : UInt256, 64 ≤ i.val →
      Finmap.lookup i e₆.machine_state.memory = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi
    have := accOut_junk_window (σ := e₅) (key := k₂) (base := r₅) (i := i) hi
    rw [h₆] at this
    rw [this]; exact hj₅ i hi
  have hj₇ : ∀ i : UInt256, 64 ≤ i.val →
      Finmap.lookup i e₇.machine_state.memory = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi
    have := accOut_junk_window (σ := e₆) (key := k₃) (base := r₆) (i := i) hi
    rw [h₇] at this
    rw [this]; exact hj₆ i hi
  have hjmid : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σmid.machine_state.memory
        = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi hi'
    rw [hmem i hi hi']; exact hj₇ i hi
  -- LEVEL 1 of the re-run: cache hit at the first run's level-1 preimage.
  have hI₁ : accInterval σmid k₁ b = accInterval σ₀ k₁ b :=
    accInterval_eq (fun i hi hi' => by rw [hjmid i hi hi'])
  have h11' : accOut σmid k₁ b = (r₅, (σmid.mstore 0 k₁).mstore 32 b) :=
    accOut_of_cached (by rw [hI₁]; exact hm₅)
  have hr₁₁ : r₁₁ = r₅ := by
    rw [h₁₁] at h11'
    exact (Prod.mk.injEq .. ▸ h11').1
  have he₁₁ : e₁₁ = (σmid.mstore 0 k₁).mstore 32 b := by
    rw [h₁₁] at h11'
    exact (Prod.mk.injEq .. ▸ h11').2
  -- e₁₁ bookkeeping: cache = σmid's; junk window = σmid's = σ₀'s.
  have he₁₁_map : e₁₁.keccak_map = σmid.keccak_map := by rw [he₁₁]; rfl
  have hj₁₁ : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i e₁₁.machine_state.memory
        = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi hi'
    rw [he₁₁]
    have hms : (((σmid.mstore 0 k₁).mstore 32 b)).machine_state
        = (σmid.machine_state.updateMemory 0 k₁).updateMemory 32 b := rfl
    have hout32 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 32 := by
      intro k hk he
      have : i.val = k + 32 := by
        rw [he, val_coe_add k 32 hk (by rw [val_32]; norm_num)]
        rw [val_32]
      omega
    have hout0 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 0 := by
      intro k hk he
      have : i.val = k + 0 := by
        rw [he, val_coe_add k 0 hk (by rw [val_0]; norm_num)]
        rw [val_0]
      omega
    rw [hms, lookup_updateMemory_outside _ 32 b i hout32,
        lookup_updateMemory_outside _ 0 k₁ i hout0]
    exact hjmid i hi hi'
  -- LEVEL 2 of the re-run: same key k₂ and (by hr₁₁) same base r₅; junk windows
  -- agree (both are σ₀'s); the level-2 preimage is cached to r₆ in e₁₁.
  have hI₂ : accInterval e₁₁ k₂ r₅ = accInterval e₅ k₂ r₅ :=
    accInterval_eq (fun i hi hi' => by rw [hj₁₁ i hi hi', hj₅ i hi])
  have h12' : accOut e₁₁ k₂ r₅ = (r₆, (e₁₁.mstore 0 k₂).mstore 32 r₅) :=
    accOut_of_cached (by rw [hI₂, he₁₁_map]; exact hm₆)
  have h₁₂' : accOut e₁₁ k₂ r₅ = (r₁₂, e₁₂) := by rw [← hr₁₁]; exact h₁₂
  have hr₁₂ : r₁₂ = r₆ := by
    rw [h₁₂'] at h12'
    exact (Prod.mk.injEq .. ▸ h12').1
  have he₁₂ : e₁₂ = (e₁₁.mstore 0 k₂).mstore 32 r₅ := by
    rw [h₁₂'] at h12'
    exact (Prod.mk.injEq .. ▸ h12').2
  -- e₁₂ bookkeeping.
  have he₁₂_map : e₁₂.keccak_map = σmid.keccak_map := by rw [he₁₂, ← he₁₁_map]; rfl
  have hj₁₂ : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i e₁₂.machine_state.memory
        = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi hi'
    rw [he₁₂]
    have hms : (((e₁₁.mstore 0 k₂).mstore 32 r₅)).machine_state
        = (e₁₁.machine_state.updateMemory 0 k₂).updateMemory 32 r₅ := rfl
    have hout32 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 32 := by
      intro k hk he
      have : i.val = k + 32 := by
        rw [he, val_coe_add k 32 hk (by rw [val_32]; norm_num)]
        rw [val_32]
      omega
    have hout0 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 0 := by
      intro k hk he
      have : i.val = k + 0 := by
        rw [he, val_coe_add k 0 hk (by rw [val_0]; norm_num)]
        rw [val_0]
      omega
    rw [hms, lookup_updateMemory_outside _ 32 r₅ i hout32,
        lookup_updateMemory_outside _ 0 k₂ i hout0]
    exact hj₁₁ i hi hi'
  -- LEVEL 3 of the re-run.
  have hI₃ : accInterval e₁₂ k₃ r₆ = accInterval e₆ k₃ r₆ :=
    accInterval_eq (fun i hi hi' => by rw [hj₁₂ i hi hi', hj₆ i hi])
  have h13' : accOut e₁₂ k₃ r₆ = (r₇, (e₁₂.mstore 0 k₃).mstore 32 r₆) :=
    accOut_of_cached (by rw [hI₃, he₁₂_map]; exact hm₇)
  have h₁₃' : accOut e₁₂ k₃ r₆ = (r₁₃, e₁₃) := by rw [← hr₁₂]; exact h₁₃
  have hr₁₃ : r₁₃ = r₇ := by
    rw [h₁₃'] at h13'
    exact (Prod.mk.injEq .. ▸ h13').1
  exact ⟨hr₁₁, hr₁₂, hr₁₃⟩

/-- **2-level accessor-chain determinism** (the `mapping[key₁][key₂]` shape, e.g.
`AtomicFlowManager._state[flowId][bundleHash]`): re-running the 2-level nested
accessor chain with the same keys `(k₁, k₂)` and base `b` returns the same two
slots, under the same frame/cache/cleanliness hypotheses as the 3-level form. -/
theorem accessor_chain2_deterministic
    {σ₀ σmid : EVMState} {k₁ k₂ b : UInt256}
    {r₅ r₆ r₁₁ r₁₂ : UInt256} {e₅ e₆ e₁₁ e₁₂ : EVMState}
    (h₅ : accOut σ₀ k₁ b = (r₅, e₅))
    (h₆ : accOut e₅ k₂ r₅ = (r₆, e₆))
    (hmem : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σmid.machine_state.memory
        = Finmap.lookup i e₆.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I e₆.keccak_map = some w → Finmap.lookup I σmid.keccak_map = some w)
    (h₁₁ : accOut σmid k₁ b = (r₁₁, e₁₁))
    (h₁₂ : accOut e₁₁ k₂ r₁₁ = (r₁₂, e₁₂))
    (hclean : e₆.hash_collision = false) :
    r₁₁ = r₅ ∧ r₁₂ = r₆ := by
  -- First-run cleanliness propagates backward.
  have hclean₅ : e₅.hash_collision = false := by
    have := accOut_clean_backward (σ := e₅) (key := k₂) (base := r₅)
      (by rw [h₆]; exact hclean)
    exact this
  -- First-run cache facts.
  have hc₅ : Finmap.lookup (accInterval σ₀ k₁ b) e₅.keccak_map = some r₅ := by
    have := accOut_caches_of_clean (σ := σ₀) (key := k₁) (base := b)
      (by rw [h₅]; exact hclean₅)
    rw [h₅] at this; exact this
  have hc₆ : Finmap.lookup (accInterval e₅ k₂ r₅) e₆.keccak_map = some r₆ := by
    have := accOut_caches_of_clean (σ := e₅) (key := k₂) (base := r₅)
      (by rw [h₆]; exact hclean)
    rw [h₆] at this; exact this
  have hc₅₆ : Finmap.lookup (accInterval σ₀ k₁ b) e₆.keccak_map = some r₅ := by
    have := accOut_lookup_mono (σ := e₅) (key := k₂) (base := r₅) hc₅
    rw [h₆] at this; exact this
  have hm₅ := hmono _ _ hc₅₆
  have hm₆ := hmono _ _ hc₆
  -- Junk-window bookkeeping.
  have hj₅ : ∀ i : UInt256, 64 ≤ i.val →
      Finmap.lookup i e₅.machine_state.memory = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi
    have := accOut_junk_window (σ := σ₀) (key := k₁) (base := b) (i := i) hi
    rw [h₅] at this; exact this
  have hj₆ : ∀ i : UInt256, 64 ≤ i.val →
      Finmap.lookup i e₆.machine_state.memory = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi
    have := accOut_junk_window (σ := e₅) (key := k₂) (base := r₅) (i := i) hi
    rw [h₆] at this
    rw [this]; exact hj₅ i hi
  have hjmid : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σmid.machine_state.memory
        = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi hi'
    rw [hmem i hi hi']; exact hj₆ i hi
  -- LEVEL 1 of the re-run: cache hit.
  have hI₁ : accInterval σmid k₁ b = accInterval σ₀ k₁ b :=
    accInterval_eq (fun i hi hi' => by rw [hjmid i hi hi'])
  have h11' : accOut σmid k₁ b = (r₅, (σmid.mstore 0 k₁).mstore 32 b) :=
    accOut_of_cached (by rw [hI₁]; exact hm₅)
  have hr₁₁ : r₁₁ = r₅ := by
    rw [h₁₁] at h11'
    exact (Prod.mk.injEq .. ▸ h11').1
  have he₁₁ : e₁₁ = (σmid.mstore 0 k₁).mstore 32 b := by
    rw [h₁₁] at h11'
    exact (Prod.mk.injEq .. ▸ h11').2
  have he₁₁_map : e₁₁.keccak_map = σmid.keccak_map := by rw [he₁₁]; rfl
  have hj₁₁ : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i e₁₁.machine_state.memory
        = Finmap.lookup i σ₀.machine_state.memory := by
    intro i hi hi'
    rw [he₁₁]
    have hms : (((σmid.mstore 0 k₁).mstore 32 b)).machine_state
        = (σmid.machine_state.updateMemory 0 k₁).updateMemory 32 b := rfl
    have hout32 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 32 := by
      intro k hk he
      have : i.val = k + 32 := by
        rw [he, val_coe_add k 32 hk (by rw [val_32]; norm_num)]
        rw [val_32]
      omega
    have hout0 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 0 := by
      intro k hk he
      have : i.val = k + 0 := by
        rw [he, val_coe_add k 0 hk (by rw [val_0]; norm_num)]
        rw [val_0]
      omega
    rw [hms, lookup_updateMemory_outside _ 32 b i hout32,
        lookup_updateMemory_outside _ 0 k₁ i hout0]
    exact hjmid i hi hi'
  -- LEVEL 2 of the re-run: cache hit at the first run's level-2 preimage.
  have hI₂ : accInterval e₁₁ k₂ r₅ = accInterval e₅ k₂ r₅ :=
    accInterval_eq (fun i hi hi' => by rw [hj₁₁ i hi hi', hj₅ i hi])
  have h12' : accOut e₁₁ k₂ r₅ = (r₆, (e₁₁.mstore 0 k₂).mstore 32 r₅) :=
    accOut_of_cached (by rw [hI₂, he₁₁_map]; exact hm₆)
  have h₁₂' : accOut e₁₁ k₂ r₅ = (r₁₂, e₁₂) := by rw [← hr₁₁]; exact h₁₂
  have hr₁₂ : r₁₂ = r₆ := by
    rw [h₁₂'] at h12'
    exact (Prod.mk.injEq .. ▸ h12').1
  exact ⟨hr₁₁, hr₁₂⟩

/-! ## Symbolic-address memory lemmas

The window lemmas above are used at the concrete scratch addresses `0` and
`32`.  Merkle-leaf hashing (`IndexedMerkleTree.hashLeaf`) writes at the
*symbolic* free pointer, so we generalize: any non-wrapping 32-byte window has
distinct addresses, `mstore`/`mload` round-trips at a symbolic address, and
writes outside a value-range are invisible. -/

/-- `window a` has no duplicates whenever the 32-byte window does not wrap. -/
theorem window_nodup (a : UInt256) (ha : a.val + 32 ≤ 2 ^ 256) : (window a).Nodup := by
  unfold window
  refine List.Nodup.map_on ?_ (List.nodup_range 32)
  intro j hj k hk he
  rw [List.mem_range] at hj
  rw [List.mem_range] at hk
  have hv := congrArg Fin.val he
  rw [val_coe_add j a hj ha, val_coe_add k a hk ha] at hv
  omega

/-- Reading outside a non-wrapping window (by value bounds) is unchanged. -/
theorem lookup_updateMemory_outside_val (m : MachineState) (a v i : UInt256)
    (ha : a.val + 32 ≤ 2 ^ 256)
    (h : i.val < a.val ∨ a.val + 32 ≤ i.val) :
    Finmap.lookup i (m.updateMemory a v).memory = Finmap.lookup i m.memory := by
  apply lookup_updateMemory_outside
  intro k hk he
  have hval := congrArg Fin.val he
  rw [val_coe_add k a hk ha] at hval
  omega

/-- Reading back the whole inserted address list, in order, recovers the bytes
(when the addresses are `Nodup` and the lengths match).  (Local copy of the
`KeccakInjective` helper — this file stays free of the axiom module.) -/
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
        have h1 : Finmap.lookup b
            (List.foldl (flip id) m (List.zipWith Finmap.insert (b :: bs) (c :: cs))) = some c := by
          simp only [List.zipWith_cons_cons, List.foldl_cons, flip, id]
          rw [lookup_fold_not_mem (Finmap.insert b c m) b bs cs hnm]
          exact Finmap.lookup_insert m
        rw [h1]; rfl
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

/-- `fromBytes! ∘ toBytes!` is the identity on the value (as a `ℕ`).  (Local
copy of the `KeccakInjective` helper.) -/
theorem fromBytes_toBytes (v : UInt256) :
    Clear.UInt256.fromBytes! (Clear.UInt256.toBytes! v) = v.val := by
  unfold Clear.UInt256.fromBytes!
  have hlen : (Clear.UInt256.toBytes! v).length = 32 := Clear.UInt256.length_toBytes!
  rw [show (32 : ℕ) = (Clear.UInt256.toBytes! v).length from hlen.symm, List.take_length]
  unfold Clear.UInt256.toBytes!
  simp

/-- **General `mstore`/`mload` round-trip** at a symbolic, non-wrapping address:
writing `v` at `a` and reading the word back at `a` returns `v`. -/
theorem lookupMemory_updateMemory_self' (m : MachineState) (a v : UInt256)
    (ha : a.val + 32 ≤ 2 ^ 256) :
    (m.updateMemory a v).lookupMemory a = v := by
  unfold MachineState.lookupMemory
  have hoffs : UInt256.offsets = (List.range 32).map (fun k : ℕ => ((↑k : UInt256))) := by
    decide
  have hread : UInt256.offsets.map
        (fun i => (Finmap.lookup (a + i) (m.updateMemory a v).memory).get!)
      = (window a).map (fun x => (Finmap.lookup x (m.updateMemory a v).memory).get!) := by
    rw [hoffs]
    unfold window
    rw [List.map_map, List.map_map]
    apply List.map_congr
    intro k _
    simp only [Function.comp]
    rw [add_comm]
  rw [hread]
  have hlen : (window a).length = (Clear.UInt256.toBytes! v).length := by
    unfold window
    simp [Clear.UInt256.length_toBytes!]
  have hfold := read_fold_eq m.memory (window a) (Clear.UInt256.toBytes! v) hlen
    (window_nodup a ha)
  rw [updateMemory_memory]
  rw [hfold, fromBytes_toBytes]
  exact Fin.cast_val_eq_self v

/-- **Word-level write framing**: a 32-byte write at `a` leaves the word read at
`i` unchanged when the two (non-wrapping) windows are disjoint. -/
theorem lookupMemory_updateMemory_outside (m : MachineState) (a v i : UInt256)
    (ha : a.val + 32 ≤ 2 ^ 256) (hi : i.val + 32 ≤ 2 ^ 256)
    (hdisj : i.val + 32 ≤ a.val ∨ a.val + 32 ≤ i.val) :
    (m.updateMemory a v).lookupMemory i = m.lookupMemory i := by
  unfold MachineState.lookupMemory
  have hoffs : UInt256.offsets = (List.range 32).map (fun k : ℕ => ((↑k : UInt256))) := by
    decide
  refine congrArg (fun l => ((Clear.UInt256.fromBytes! l : ℕ) : UInt256)) ?_
  rw [hoffs, List.map_map, List.map_map]
  apply List.map_congr
  intro k hk
  rw [List.mem_range] at hk
  simp only [Function.comp]
  have hs := uint256_size_eq
  have hkv : ((↑k : UInt256)).val = k := Fin.val_cast_of_lt (by omega)
  have hio : (i + (↑k : UInt256)).val = i.val + k := by
    have h1 : (i + (↑k : UInt256)).val = (i.val + ((↑k : UInt256)).val) % UInt256.size := rfl
    rw [h1, hkv]
    exact Nat.mod_eq_of_lt (by omega)
  rw [lookup_updateMemory_outside_val m a v (i + (↑k : UInt256)) (by omega)
      (by rw [hio]; omega)]

/-- **Interval equality at a symbolic window**: `mkInterval m p n` depends only
on the bytes `[p, p+n+31)` (each of the `n` words reads 32 bytes), so byte
agreement there gives interval equality.  Generalizes the concrete
`accessor_interval_eq` to arbitrary non-wrapping windows (e.g. the 96-byte
leaf-hash region). -/
theorem mkInterval_eq_of_byte_agree
    {m₁ m₂ : MachineState} {p n : UInt256}
    (hnw : p.val + n.val + 31 ≤ 2 ^ 256)
    (hagree : ∀ i : UInt256, p.val ≤ i.val → i.val < p.val + n.val + 31 →
      Finmap.lookup i m₁.memory = Finmap.lookup i m₂.memory) :
    mkInterval m₁ p n = mkInterval m₂ p n := by
  unfold EVMState.mkInterval
  apply List.map_congr
  intro j hj
  rw [List.mem_map] at hj
  obtain ⟨j', hj', rfl⟩ := hj
  rw [List.mem_range'_1] at hj'
  have hs := uint256_size_eq
  have hjv : (Fin.ofNat j' : UInt256).val = j' := by
    have hv : (Fin.ofNat j' : UInt256).val = j' % UInt256.size := rfl
    rw [hv, Nat.mod_eq_of_lt (by omega)]
  -- word congruence over the 32 byte reads
  unfold MachineState.lookupMemory
  have hoffs : UInt256.offsets = (List.range 32).map (fun k : ℕ => ((↑k : UInt256))) := by
    decide
  refine congrArg (fun l => ((Clear.UInt256.fromBytes! l : ℕ) : UInt256)) ?_
  rw [hoffs, List.map_map, List.map_map]
  apply List.map_congr
  intro k hk
  rw [List.mem_range] at hk
  simp only [Function.comp]
  have hkv : ((↑k : UInt256)).val = k := Fin.val_cast_of_lt (by omega)
  refine congrArg Option.get! (hagree _ ?_ ?_) <;>
  · rw [Fin.val_add, hjv, hkv]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Generic keccak replay determinism** at a symbolic window: if the second
state's interval equals the first's, the first call's cache entry survived,
and the first call was collision-free, the second call returns the same hash. -/
theorem keccakOut_deterministic
    {σ₁ σ₂ : EVMState} {p n : UInt256}
    (hI : mkInterval σ₂.machine_state p n = mkInterval σ₁.machine_state p n)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I (keccakOut σ₁ p n).2.keccak_map = some w →
        Finmap.lookup I σ₂.keccak_map = some w)
    (hclean : (keccakOut σ₁ p n).2.hash_collision = false) :
    (keccakOut σ₂ p n).1 = (keccakOut σ₁ p n).1 := by
  have hc := keccakOut_caches_of_clean hclean
  have hm := hmono _ _ hc
  rw [keccakOut_of_cached (by rw [hI]; exact hm)]

/-- An `accOut` step (scratch writes at `[0, 64)` + keccak) leaves any word at
`96 ≤ a` unchanged — the frame for reading array data across hash steps. -/
theorem accOut_mload_high
    {σ : EVMState} {x y a : UInt256}
    (ha : 96 ≤ a.val) (hnw : a.val + 32 ≤ 2 ^ 256) :
    (accOut σ x y).2.mload a = σ.mload a := by
  show (accOut σ x y).2.machine_state.lookupMemory a = σ.machine_state.lookupMemory a
  rw [show (accOut σ x y).2.machine_state
      = ((σ.mstore 0 x).mstore 32 y).machine_state from keccakOut_machine_state _ _ _]
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h0v : ((0 : UInt256)).val = 0 := by decide
  rw [show ((σ.mstore 0 x).mstore 32 y).machine_state
      = (σ.machine_state.updateMemory 0 x).updateMemory 32 y from rfl]
  rw [lookupMemory_updateMemory_outside _ 32 y a (by rw [h32v]; norm_num) hnw
      (by right; rw [h32v]; omega)]
  rw [lookupMemory_updateMemory_outside _ 0 x a (by rw [h0v]; norm_num) hnw
      (by right; rw [h0v]; omega)]

/-- **Cross-state accessor cache hit.**  If a *different* state `σ₂` already
caches the accessor preimage that `σ₁` would produce (mapped to `r`), and the
two states agree on the junk window `[64, 95)` — the only preimage bytes the two
scratch `mstore`s do not overwrite — then `accOut` on `σ₂` is a cache hit
returning exactly `r`.

This is the abstract, `generated`-free form of the cross-evm agreement atom the
builder–verifier fold relies on: the verifier evm `σ₂` need only carry the
walk evm `σ₁`'s cache entry and agree on the junk window; cleanliness of the
second run is *not* required.  Axiom-free. -/
theorem accOut_of_cached_frame
    {σ₁ σ₂ : EVMState} {key base r : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory)
    (hcache : Finmap.lookup (accInterval σ₁ key base) σ₂.keccak_map = some r) :
    accOut σ₂ key base = (r, (σ₂.mstore 0 key).mstore 32 base) := by
  apply accOut_of_cached
  rw [show accInterval σ₂ key base = accInterval σ₁ key base from
      accInterval_eq (fun i h1 h2 => (hframe i h1 h2).symm)]
  exact hcache

/-- Value corollary of `accOut_of_cached_frame`: under the same hypotheses the
cross-state accessor step *produces* exactly the cached hash `r`. -/
theorem accOut_agree_value
    {σ₁ σ₂ : EVMState} {key base r : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory)
    (hcache : Finmap.lookup (accInterval σ₁ key base) σ₂.keccak_map = some r) :
    (accOut σ₂ key base).1 = r := by
  rw [accOut_of_cached_frame hframe hcache]

/-- **Cross-state accessor determinism.**  Two accessor runs with the same
`(key, base)` from junk-window-agreeing states produce the same hash, provided
the second state `σ₂` transports the first run's post-state cache entry for the
preimage and the first run's post-state is collision-free.  The `accOut`
specialization of `keccakOut_deterministic`; the second run needs no cleanliness
assumption — it hits the cache.  Axiom-free. -/
theorem accOut_deterministic
    {σ₁ σ₂ : EVMState} {key base : UInt256}
    (hframe : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory)
    (hmono : ∀ w : UInt256,
      Finmap.lookup (accInterval σ₁ key base) (accOut σ₁ key base).2.keccak_map = some w →
        Finmap.lookup (accInterval σ₁ key base) σ₂.keccak_map = some w)
    (hclean : (accOut σ₁ key base).2.hash_collision = false) :
    (accOut σ₂ key base).1 = (accOut σ₁ key base).1 := by
  have h2 := hmono _ (accOut_caches_of_clean hclean)
  rw [accOut_of_cached_frame hframe h2]

/-- **General `mstore`/`mload` round-trip, `EVMState` level**: writing `v` at
a non-wrapping `a` and reading the word back at `a` returns `v`. -/
theorem mload_mstore_self_at (σ : EVMState) (a v : UInt256)
    (ha : a.val + 32 ≤ 2 ^ 256) :
    (σ.mstore a v).mload a = v := by
  unfold EVMState.mstore EVMState.mload EVMState.updateMemory
  exact lookupMemory_updateMemory_self' σ.machine_state a v ha

/-- **General `mstore`/`mload` framing, `EVMState` level**: a write at `a`
leaves the word read at a disjoint (non-wrapping) `i` unchanged. -/
theorem mload_mstore_outside (σ : EVMState) (a v i : UInt256)
    (ha : a.val + 32 ≤ 2 ^ 256) (hi : i.val + 32 ≤ 2 ^ 256)
    (hdisj : i.val + 32 ≤ a.val ∨ a.val + 32 ≤ i.val) :
    (σ.mstore a v).mload i = σ.mload i := by
  unfold EVMState.mstore EVMState.mload EVMState.updateMemory
  exact lookupMemory_updateMemory_outside σ.machine_state a v i ha hi hdisj

/-- **Two-write framing composite**: a read at `i` disjoint from two
(non-wrapping) writes passes through both. -/
theorem mload_mstore_outside₂ (σ : EVMState) (a₁ v₁ a₂ v₂ i : UInt256)
    (ha₁ : a₁.val + 32 ≤ 2 ^ 256) (ha₂ : a₂.val + 32 ≤ 2 ^ 256)
    (hi : i.val + 32 ≤ 2 ^ 256)
    (hd₁ : i.val + 32 ≤ a₁.val ∨ a₁.val + 32 ≤ i.val)
    (hd₂ : i.val + 32 ≤ a₂.val ∨ a₂.val + 32 ≤ i.val) :
    ((σ.mstore a₁ v₁).mstore a₂ v₂).mload i = σ.mload i := by
  rw [mload_mstore_outside _ a₂ v₂ i ha₂ hi hd₂,
      mload_mstore_outside σ a₁ v₁ i ha₁ hi hd₁]

/-- The junk window `[64, 95)` survives *two* consecutive accessor steps — the
frame that lets a multi-level fold read scratch state after any number of
pair-hash steps (base atom for the fold agreement induction). -/
theorem accOut_junk_window₂
    {σ : EVMState} {k₁ b₁ k₂ b₂ : UInt256} {i : UInt256}
    (hi : 64 ≤ i.val) :
    Finmap.lookup i (accOut (accOut σ k₁ b₁).2 k₂ b₂).2.machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  rw [accOut_junk_window hi, accOut_junk_window hi]

/-- The state threaded through a multi-level pair-hash walk: each level applies
`accOut` at its own `(key, base)` and carries the *resulting* state forward.
The `(key, base)` sequence is externally supplied (in a real walk each is
determined by the running accumulator and the level sibling); the junk-window
frame below is uniform over that sequence, so this list model loses nothing. -/
def accStateFold (σ : EVMState) : List (UInt256 × UInt256) → EVMState
  | [] => σ
  | (k, b) :: rest => accStateFold (accOut σ k b).2 rest

/-- **N-STEP JUNK-WINDOW FRAME.**  The junk window `[64, 95)` survives *any*
number of pair-hash steps — the `n`-step generalization of `accOut_junk_window₂`
by induction on the level list.  This is the atom that lets a fold read scratch
state after arbitrarily many `accOut`s. -/
theorem accStateFold_junk_window {i : UInt256} (hi : 64 ≤ i.val) :
    ∀ (pairs : List (UInt256 × UInt256)) (σ : EVMState),
      Finmap.lookup i (accStateFold σ pairs).machine_state.memory
        = Finmap.lookup i σ.machine_state.memory
  | [], _ => rfl
  | (k, b) :: rest, σ => by
      simp only [accStateFold]
      rw [accStateFold_junk_window hi rest (accOut σ k b).2, accOut_junk_window hi]

/-- **FOLD AGREEMENT ON THE JUNK WINDOW.**  Two states that agree on a junk
index `i ≥ 64` still agree there after running *arbitrary* (and possibly
different) pair-hash folds — the builder's walk and the verifier's replay may
differ in length and content, yet neither disturbs the shared scratch window.
The precise sense in which the fold is "agreement-preserving". -/
theorem accStateFold_junk_agree
    {σ₁ σ₂ : EVMState} {pairs₁ pairs₂ : List (UInt256 × UInt256)}
    {i : UInt256} (hi : 64 ≤ i.val)
    (h : Finmap.lookup i σ₁.machine_state.memory
      = Finmap.lookup i σ₂.machine_state.memory) :
    Finmap.lookup i (accStateFold σ₁ pairs₁).machine_state.memory
      = Finmap.lookup i (accStateFold σ₂ pairs₂).machine_state.memory := by
  rw [accStateFold_junk_window hi pairs₁ σ₁, accStateFold_junk_window hi pairs₂ σ₂]
  exact h

/-- **FOLD PHASE COMPOSITION.**  Threading a concatenated level list is the same
as threading the two segments in turn — the pure shape behind composing a walk's
phases (update walk ++ pad ++ push walk) into one state evolution. -/
theorem accStateFold_append (σ : EVMState) (p q : List (UInt256 × UInt256)) :
    accStateFold σ (p ++ q) = accStateFold (accStateFold σ p) q := by
  induction p generalizing σ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨k, b⟩ := hd
      simp only [List.cons_append, accStateFold]
      exact ih (accOut σ k b).2

end Clear.KeccakDeterminism
