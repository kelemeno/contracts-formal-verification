import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.IMTAbstract
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user
import specs.KeccakInjective

/-
  IMT FIDELITY, slice 1 — the storage-to-abstract leaf abstraction.

  Goal of the fidelity track: "the Yul commitment tree implements the
  abstract `imtInsert`/`Evolution`", so that the cross-chain atomicity core
  (#60, `delivered_leg_available_forever`) applies to the deployed code.

  This slice defines the abstraction function and proves its `sstore`
  frames:

  * `leafSlot σ i`   — the storage slot of leaf `i`: the `leaves` mapping
    lives at slot 5 (`mapping_leaves_call`), so the slot is one `accOut`
    step at `(i, 5)`;
  * `decodeLeaf σ i` — the abstract leaf at index `i`: the concrete
    `IMTLeaf` struct is `{value, nextIndex, nextValue}` at `slot`/`+1`/`+2`
    (IndexedMerkleTree.sol), and `AbsLeaf ⟨key, nextKey⟩` reads the
    `value`/`nextValue` fields (`+0`/`+2`) — the index-level link
    `nextIndex` has no abstract counterpart;
  * `leafSetOf σ`    — the abstract leaf set: `decodeLeaf` imaged over the
    leaf count (storage slot 1).

  MODEL NOTE (the cached-branch discipline): `EVMState.sstore` grows
  `used_range`, and `keccak256`'s FRESH branch picks its hash from the
  range partitioned by `used_range` — so keccak values are sstore-stable
  only on the CACHED branch.  All frames below therefore carry a
  cache hypothesis (`accInterval … ∈ keccak_map`); in the insert glue the
  mapping accessor itself caches the slot hash on first use
  (`accOut_caches_of_clean`), so the hypothesis is discharged by sequencing.

  Axiom-free.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     IMTAbstract Clear.KeccakDeterminism

set_option maxRecDepth 4000
set_option linter.dupNamespace false

/-! ### `sstore` component transparency -/

/-- `sstore` touches accounts and `used_range` only — machine state (and so
memory) is unchanged. -/
private lemma machine_state_sstore' (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).machine_state = σ.machine_state := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- `sstore` leaves the keccak cache unchanged. -/
private lemma keccak_map_sstore' (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).keccak_map = σ.keccak_map := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-! ### The cached-branch hash congruence -/

/-- If the preimage interval is cached, `keccakOut` returns the cached word
— on this branch the hash is independent of `used_range` (and hence of any
interleaved `sstore`s). -/
private lemma keccakOut_fst_cached {σ : EVMState} {p n w : UInt256}
    (h : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = some w) :
    (keccakOut σ p n).1 = w := by
  unfold keccakOut EVMState.keccak256
  simp only [h]

/-! ### The abstraction function -/

/-- The storage slot of leaf `i`: the `leaves` mapping at base slot 5. -/
def leafSlot (σ : EVMState) (i : UInt256) : UInt256 :=
  (accOut σ i 5).1

/-- The abstract leaf at index `i`: the `value`/`nextValue` fields of the
concrete `IMTLeaf` struct. -/
def decodeLeaf (σ : EVMState) (i : UInt256) : AbsLeaf :=
  ⟨σ.sload (leafSlot σ i), σ.sload (leafSlot σ i + 2)⟩

/-- The abstract leaf set: `decodeLeaf` over the leaf count (slot 1). -/
def leafSetOf (σ : EVMState) : Finset AbsLeaf :=
  (Finset.range (σ.sload 1).val).image (fun (n : ℕ) => decodeLeaf σ (n : UInt256))

/-! ### `sstore` frames -/

/-- **The mapping slot is `sstore`-invariant once cached.** -/
theorem leafSlot_sstore {σ : EVMState} {a v i w : UInt256}
    (hc : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some w) :
    leafSlot (σ.sstore a v) i = leafSlot σ i := by
  unfold leafSlot accOut
  have hms : (((σ.sstore a v).mstore 0 i).mstore 32 5).machine_state
      = ((σ.mstore 0 i).mstore 32 5).machine_state := by
    show ((σ.sstore a v).machine_state.updateMemory 0 i).updateMemory 32 5
      = (σ.machine_state.updateMemory 0 i).updateMemory 32 5
    rw [machine_state_sstore']
  have hkm : (((σ.sstore a v).mstore 0 i).mstore 32 5).keccak_map
      = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore, keccak_map_sstore']
  have hkm0 : ((σ.mstore 0 i).mstore 32 5).keccak_map = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore]
  have hc' : Finmap.lookup
      (mkInterval ((σ.mstore 0 i).mstore 32 5).machine_state 0 64)
      σ.keccak_map = some w := hc
  rw [keccakOut_fst_cached (by rw [hms, hkm]; exact hc'),
      keccakOut_fst_cached (by rw [hkm0]; exact hc')]

/-- **Leaf decoding is `sstore`-invariant outside the leaf's two abstract
field slots** (cached mapping hash; the write may target other leaves, the
count, or any node array). -/
theorem decodeLeaf_sstore_outside {σ : EVMState} {a v i w : UInt256}
    (hc : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some w)
    (h0 : a ≠ leafSlot σ i) (h2 : a ≠ leafSlot σ i + 2) :
    decodeLeaf (σ.sstore a v) i = decodeLeaf σ i := by
  unfold decodeLeaf
  rw [leafSlot_sstore hc, sload_sstore_ne h0, sload_sstore_ne h2]

/-- **The leaf count is `sstore`-invariant off slot 1.** -/
theorem leafCount_sstore {σ : EVMState} {a v : UInt256} (h1 : a ≠ 1) :
    (σ.sstore a v).sload 1 = σ.sload 1 :=
  sload_sstore_ne h1

/-! ### Cache transport across `sstore` -/

/-- The accessor preimage interval is `sstore`-invariant (it reads memory
only). -/
private lemma accInterval_sstore (σ : EVMState) (a v key base : UInt256) :
    accInterval (σ.sstore a v) key base = accInterval σ key base := by
  unfold accInterval
  have hms : (((σ.sstore a v).mstore 0 key).mstore 32 base).machine_state
      = ((σ.mstore 0 key).mstore 32 base).machine_state := by
    show ((σ.sstore a v).machine_state.updateMemory 0 key).updateMemory 32 base
      = (σ.machine_state.updateMemory 0 key).updateMemory 32 base
    rw [machine_state_sstore']
  rw [hms]

/-- A cached accessor hash stays cached across any `sstore`. -/
private lemma cache_sstore {σ : EVMState} {a v key w : UInt256}
    (hc : Finmap.lookup (accInterval σ key 5) σ.keccak_map = some w) :
    Finmap.lookup (accInterval (σ.sstore a v) key 5)
        (σ.sstore a v).keccak_map = some w := by
  rw [accInterval_sstore, keccak_map_sstore']
  exact hc

/-- `a + k ≠ a` for nonzero `k` (`UInt256` group arithmetic). -/
private lemma add_k_ne_self {a k : UInt256} (hk : k ≠ 0) : a + k ≠ a := by
  intro h
  have h' : a + k = a + 0 := by rw [h, add_zero]
  exact hk (add_left_cancel h')

/-! ### The write agreement: a freshly written struct decodes exactly -/

/-- **WRITE AGREEMENT** — after the three-field struct write of leaf `n`
(`value := v`, `nextIndex := ni`, `nextValue := nv`), the abstract decode of
index `n` is exactly `⟨v, nv⟩`.  Cached mapping hash; executing account
present (an absent account makes `sstore` a no-op). -/
theorem decodeLeaf_after_write {σ : EVMState} {n v ni nv w : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hc : Finmap.lookup (accInterval σ n 5) σ.keccak_map = some w) :
    decodeLeaf (((σ.sstore (leafSlot σ n) v).sstore
        (leafSlot σ n + 1) ni).sstore (leafSlot σ n + 2) nv) n
      = ⟨v, nv⟩ := by
  have hacc1 := acct_sstore (a := leafSlot σ n) (v := v) hacc
  have hacc2 := acct_sstore (a := leafSlot σ n + 1) (v := ni) hacc1
  have hc1 := cache_sstore (a := leafSlot σ n) (v := v) hc
  have hc2 := cache_sstore (a := leafSlot σ n + 1) (v := ni) hc1
  have hsl1 : leafSlot (σ.sstore (leafSlot σ n) v) n = leafSlot σ n :=
    leafSlot_sstore hc
  have hsl2 : leafSlot ((σ.sstore (leafSlot σ n) v).sstore
      (leafSlot σ n + 1) ni) n = leafSlot σ n := by
    rw [leafSlot_sstore hc1, hsl1]
  have hsl3 : leafSlot (((σ.sstore (leafSlot σ n) v).sstore
      (leafSlot σ n + 1) ni).sstore (leafSlot σ n + 2) nv) n
      = leafSlot σ n := by
    rw [leafSlot_sstore hc2, hsl2]
  unfold decodeLeaf
  rw [hsl3]
  have h2 : ((((σ.sstore (leafSlot σ n) v).sstore
      (leafSlot σ n + 1) ni).sstore (leafSlot σ n + 2) nv)).sload
        (leafSlot σ n + 2) = nv :=
    sload_sstore_self hacc2
  have h0 : ((((σ.sstore (leafSlot σ n) v).sstore
      (leafSlot σ n + 1) ni).sstore (leafSlot σ n + 2) nv)).sload
        (leafSlot σ n) = v := by
    rw [sload_sstore_ne (add_k_ne_self (by decide)),
        sload_sstore_ne (add_k_ne_self (by decide))]
    exact sload_sstore_self hacc
  rw [h0, h2]

/-! ### The set-level write equation -/

/-- **INSERT AGREEMENT, storage side** — the three-field struct write at the
current count followed by the count bump grows the abstract leaf set by
exactly the decoded new leaf:
`leafSetOf (write ∘ bump) = insert ⟨v, nv⟩ (leafSetOf σ)`.

The slot-disjointness facts are explicit hypotheses (to be discharged at
composition time by keccak injectivity: distinct mapping keys give distinct
slot hashes, hashes avoid the small scalar slots, and the `+1/+2` field
offsets of distinct 3-word windows stay disjoint). -/
theorem leafSetOf_after_write {σ : EVMState} {v ni nv w : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hc : Finmap.lookup (accInterval σ (σ.sload 1) 5) σ.keccak_map = some w)
    (hnw : (σ.sload 1).val + 1 < 2 ^ 256)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ wm, Finmap.lookup (accInterval σ (m : UInt256) 5) σ.keccak_map = some wm)
    (hdisj0 : ∀ m : ℕ, m < (σ.sload 1).val →
      leafSlot σ (σ.sload 1) ≠ leafSlot σ (m : UInt256)
      ∧ leafSlot σ (σ.sload 1) ≠ leafSlot σ (m : UInt256) + 2)
    (hdisj1 : ∀ m : ℕ, m < (σ.sload 1).val →
      leafSlot σ (σ.sload 1) + 1 ≠ leafSlot σ (m : UInt256)
      ∧ leafSlot σ (σ.sload 1) + 1 ≠ leafSlot σ (m : UInt256) + 2)
    (hdisj2 : ∀ m : ℕ, m < (σ.sload 1).val →
      leafSlot σ (σ.sload 1) + 2 ≠ leafSlot σ (m : UInt256)
      ∧ leafSlot σ (σ.sload 1) + 2 ≠ leafSlot σ (m : UInt256) + 2)
    (hone : ∀ m : ℕ, m < (σ.sload 1).val →
      (1 : UInt256) ≠ leafSlot σ (m : UInt256)
      ∧ (1 : UInt256) ≠ leafSlot σ (m : UInt256) + 2)
    (h1a : (1 : UInt256) ≠ leafSlot σ (σ.sload 1))
    (h1b : (1 : UInt256) ≠ leafSlot σ (σ.sload 1) + 2) :
    leafSetOf ((((σ.sstore (leafSlot σ (σ.sload 1)) v).sstore
        (leafSlot σ (σ.sload 1) + 1) ni).sstore
        (leafSlot σ (σ.sload 1) + 2) nv).sstore 1 (σ.sload 1 + 1))
      = insert (⟨v, nv⟩ : AbsLeaf) (leafSetOf σ) := by
  set c := σ.sload 1 with hcdef
  set σ₁ := σ.sstore (leafSlot σ c) v with hσ₁
  set σ₂ := σ₁.sstore (leafSlot σ c + 1) ni with hσ₂
  set σ₃ := σ₂.sstore (leafSlot σ c + 2) nv with hσ₃
  set σ₄ := σ₃.sstore 1 (c + 1) with hσ₄
  have hacc1 := acct_sstore (a := leafSlot σ c) (v := v) hacc
  have hacc2 := acct_sstore (a := leafSlot σ c + 1) (v := ni) hacc1
  have hacc3 := acct_sstore (a := leafSlot σ c + 2) (v := nv) hacc2
  -- the count after the writes and the bump
  have hcount : σ₄.sload 1 = c + 1 := by
    rw [hσ₄]
    exact sload_sstore_self hacc3
  have hcval : (σ₄.sload 1).val = c.val + 1 := by
    rw [hcount]
    show (c.val + (1 : UInt256).val) % 2 ^ 256 = c.val + 1
    have h1v : (1 : UInt256).val = 1 := rfl
    rw [h1v]
    exact Nat.mod_eq_of_lt hnw
  -- per-index stability below the count
  have hstab : ∀ m : ℕ, m < c.val →
      decodeLeaf σ₄ (m : UInt256) = decodeLeaf σ (m : UInt256) := by
    intro m hm
    obtain ⟨wm, hcm⟩ := hcaches m hm
    have hcm1 := cache_sstore (a := leafSlot σ c) (v := v) hcm
    have hcm2 := cache_sstore (a := leafSlot σ c + 1) (v := ni) hcm1
    have hcm3 := cache_sstore (a := leafSlot σ c + 2) (v := nv) hcm2
    have hsl1 : leafSlot σ₁ (m : UInt256) = leafSlot σ (m : UInt256) :=
      leafSlot_sstore hcm
    have hsl2 : leafSlot σ₂ (m : UInt256) = leafSlot σ (m : UInt256) := by
      rw [hσ₂, leafSlot_sstore hcm1, hsl1]
    have hsl3 : leafSlot σ₃ (m : UInt256) = leafSlot σ (m : UInt256) := by
      rw [hσ₃, leafSlot_sstore hcm2, hsl2]
    have e4 : decodeLeaf σ₄ (m : UInt256) = decodeLeaf σ₃ (m : UInt256) := by
      rw [hσ₄]
      exact decodeLeaf_sstore_outside hcm3
        (by rw [hsl3]; exact (hone m hm).1)
        (by rw [hsl3]; exact (hone m hm).2)
    have e3 : decodeLeaf σ₃ (m : UInt256) = decodeLeaf σ₂ (m : UInt256) := by
      rw [hσ₃]
      exact decodeLeaf_sstore_outside hcm2
        (by rw [hsl2]; exact (hdisj2 m hm).1)
        (by rw [hsl2]; exact (hdisj2 m hm).2)
    have e2 : decodeLeaf σ₂ (m : UInt256) = decodeLeaf σ₁ (m : UInt256) := by
      rw [hσ₂]
      exact decodeLeaf_sstore_outside hcm1
        (by rw [hsl1]; exact (hdisj1 m hm).1)
        (by rw [hsl1]; exact (hdisj1 m hm).2)
    have e1 : decodeLeaf σ₁ (m : UInt256) = decodeLeaf σ (m : UInt256) := by
      rw [hσ₁]
      exact decodeLeaf_sstore_outside hcm
        (hdisj0 m hm).1 (hdisj0 m hm).2
    rw [e4, e3, e2, e1]
  -- the new index decodes to the written leaf
  have hnewc : decodeLeaf σ₄ c = ⟨v, nv⟩ := by
    have hc3 := cache_sstore (a := leafSlot σ c + 2) (v := nv)
      (cache_sstore (a := leafSlot σ c + 1) (v := ni)
        (cache_sstore (a := leafSlot σ c) (v := v) hc))
    have hsl3 : leafSlot σ₃ c = leafSlot σ c := by
      rw [hσ₃, hσ₂, hσ₁]
      rw [leafSlot_sstore (cache_sstore (cache_sstore hc)),
          leafSlot_sstore (cache_sstore hc), leafSlot_sstore hc]
    have e4 : decodeLeaf σ₄ c = decodeLeaf σ₃ c := by
      rw [hσ₄]
      exact decodeLeaf_sstore_outside hc3
        (by rw [hsl3]; exact h1a)
        (by rw [hsl3]; exact h1b)
    rw [e4, hσ₃, hσ₂, hσ₁]
    exact decodeLeaf_after_write hacc hc
  -- assemble
  unfold leafSetOf
  rw [hcval, Finset.range_succ, Finset.image_insert]
  have hcast : ((c.val : ℕ) : UInt256) = c := Fin.cast_val_eq_self c
  rw [hcast, hnewc]
  congr 1
  exact Finset.image_congr (fun m hm => hstab m (Finset.mem_range.mp hm))

/-! ### Keccak-injectivity discharge of the slot-disjointness oracles

The trusted-base axioms (`keccak256_inj`, `keccak256_slot_sep`,
`keccak256_ne_lowSlot`, `keccak256_add_ne_lowSlot` — see
`specs/KeccakInjective.lean`) turn the cached mapping hashes into the
disjointness facts `leafSetOf_after_write` consumes. -/

/-- A cached interval makes `keccak256` succeed with the cached word. -/
private lemma keccak256_of_cached {σ : EVMState} {p n w : UInt256}
    (h : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = some w) :
    σ.keccak256 p n = some (w, σ) := by
  unfold EVMState.keccak256
  simp only [h]

/-- Two 64-byte accessor preimages differ whenever the word at address `0`
(the mapping KEY word) differs — the index-0 twin of
`mkInterval_0_64_ne_of_word32_ne`. -/
private lemma mkInterval_0_64_ne_of_word0_ne
    {ms₁ ms₂ : MachineState}
    (h0 : ms₁.lookupMemory (0 : UInt256) ≠ ms₂.lookupMemory (0 : UInt256)) :
    mkInterval ms₁ 0 64 ≠ mkInterval ms₂ 0 64 := by
  intro heq
  apply h0
  have ev : ∀ ms : MachineState,
      (mkInterval ms 0 64).get? 0 = some (ms.lookupMemory (0 : UInt256)) := by
    intro ms
    unfold Clear.EVMState.mkInterval
    simp only [List.get?_map]
    have hidx : (List.range' (↑(0 : UInt256)) (↑(64 : UInt256))).get? 0
        = some ↑(0 : UInt256) := by decide
    rw [hidx]
    rfl
  have h := ev ms₁
  rw [heq, ev ms₂] at h
  exact (Option.some.inj h).symm

/-- The accessor scratch reads the key back at address `0`. -/
private lemma accWord0 (σ : EVMState) (key base : UInt256) :
    ((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory (0 : UInt256)
      = key := by
  show ((σ.mstore 0 key).mstore 32 base).mload 0 = key
  rw [mload_mstore_outside _ _ _ _ (by decide) (by decide) (Or.inl (by decide))]
  exact mload_mstore_self_at σ 0 key (by decide)

/-- Distinct keys give distinct accessor preimage intervals. -/
private lemma accInterval_ne {σ₁ σ₂ : EVMState} {i j base : UInt256}
    (hij : i ≠ j) :
    mkInterval ((σ₁.mstore 0 i).mstore 32 base).machine_state 0 64
      ≠ mkInterval ((σ₂.mstore 0 j).mstore 32 base).machine_state 0 64 := by
  apply mkInterval_0_64_ne_of_word0_ne
  rw [accWord0, accWord0]
  exact hij

/-- The cached-hash success witness for a leaf slot. -/
private lemma leafSlot_keccak {σ : EVMState} {i w : UInt256}
    (hc : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some w) :
    ((σ.mstore 0 i).mstore 32 5).keccak256 0 64
      = some (w, (σ.mstore 0 i).mstore 32 5)
    ∧ leafSlot σ i = w := by
  have hkm : ((σ.mstore 0 i).mstore 32 5).keccak_map = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore]
  constructor
  · exact keccak256_of_cached (by rw [hkm]; exact hc)
  · exact keccakOut_fst_cached (by rw [hkm]; exact hc)

/-- **Slot injectivity**: distinct cached keys live at distinct slots. -/
theorem leafSlot_inj {σ : EVMState} {i j wi wj : UInt256}
    (hci : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some wi)
    (hcj : Finmap.lookup (accInterval σ j 5) σ.keccak_map = some wj)
    (hij : i ≠ j) : leafSlot σ i ≠ leafSlot σ j := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  obtain ⟨hkj, hvj⟩ := leafSlot_keccak hcj
  rw [hvi, hvj]
  exact Clear.KeccakInjective.keccak256_inj hki hkj (accInterval_ne hij)

/-- **Offset separation**: a small offset of one leaf slot never hits
another leaf's slot. -/
theorem leafSlot_add_ne {σ : EVMState} {i j wi wj k : UInt256}
    (hci : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some wi)
    (hcj : Finmap.lookup (accInterval σ j 5) σ.keccak_map = some wj)
    (hij : i ≠ j) (hk : k.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i + k ≠ leafSlot σ j := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  obtain ⟨hkj, hvj⟩ := leafSlot_keccak hcj
  rw [hvi, hvj]
  exact Clear.KeccakInjective.keccak256_slot_sep hki hkj (accInterval_ne hij) hk

/-- **Two-sided offset separation** for concrete field offsets: with
`k₁.val ≤ k₂.val` both small, `slot_i + k₁ ≠ slot_j + k₂` for `i ≠ j`
(cancel `k₁`, then offset separation with `k₂ − k₁`). -/
theorem leafSlot_off_ne_off {σ : EVMState} {i j wi wj k₁ k₂ : UInt256}
    (hci : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some wi)
    (hcj : Finmap.lookup (accInterval σ j 5) σ.keccak_map = some wj)
    (hij : i ≠ j)
    (hk₁ : k₁.val < Clear.KeccakInjective.lowSlotBound)
    (hk₂ : k₂.val < Clear.KeccakInjective.lowSlotBound)
    (hle : k₁.val ≤ k₂.val) :
    leafSlot σ i + k₁ ≠ leafSlot σ j + k₂ := by
  intro heq
  have hd : ((k₂.val - k₁.val : ℕ) : UInt256).val = k₂.val - k₁.val := by
    apply Nat.mod_eq_of_lt
    calc k₂.val - k₁.val ≤ k₂.val := Nat.sub_le _ _
    _ < UInt256.size := k₂.isLt
  have hk2eq : k₁ + ((k₂.val - k₁.val : ℕ) : UInt256) = k₂ := by
    apply Fin.ext
    show (k₁.val + ((k₂.val - k₁.val : ℕ) : UInt256).val) % UInt256.size = k₂.val
    rw [hd, Nat.add_sub_cancel' hle]
    exact Nat.mod_eq_of_lt k₂.isLt
  have heq' : leafSlot σ i + k₁
      = (leafSlot σ j + ((k₂.val - k₁.val : ℕ) : UInt256)) + k₁ := by
    rw [heq]
    conv_lhs => rw [← hk2eq]
    ring
  have hcore : leafSlot σ i = leafSlot σ j + ((k₂.val - k₁.val : ℕ) : UInt256) :=
    add_right_cancel heq'
  have := leafSlot_add_ne hcj hci (Ne.symm hij)
    (k := ((k₂.val - k₁.val : ℕ) : UInt256))
    (by rw [hd]; exact lt_of_le_of_lt (Nat.sub_le _ _) hk₂)
  exact this hcore.symm

/-- **Slots avoid the reserved low slots** (count at 1, roots, sizes …). -/
theorem leafSlot_ne_low {σ : EVMState} {i w : UInt256} (c : UInt256)
    (hc : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some w)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i ≠ c := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hc
  rw [hvi]
  exact Clear.KeccakInjective.keccak256_ne_lowSlot c hki hlow

/-- **Offset slots avoid the reserved low slots.** -/
theorem leafSlot_add_ne_low {σ : EVMState} {i w : UInt256} (k c : UInt256)
    (hc : Finmap.lookup (accInterval σ i 5) σ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i + k ≠ c := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hc
  rw [hvi]
  exact Clear.KeccakInjective.keccak256_add_ne_lowSlot k c hki hk hlow

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
