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
    lives at BASE SLOT 4 (`mapping_…_5199` in the Yul; base 5 is the
    `valueToIndex` mapping — `mapping_…_5196`, whose doc comment in
    `imt_leaf_storage_user` mislabels it), so the slot is one `accOut`
    step at `(i, 4)`;
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

/-- The storage slot of leaf `i`: the `leaves` mapping at base slot 4. -/
def leafSlot (σ : EVMState) (i : UInt256) : UInt256 :=
  (accOut σ i 4).1

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
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w) :
    leafSlot (σ.sstore a v) i = leafSlot σ i := by
  unfold leafSlot accOut
  have hms : (((σ.sstore a v).mstore 0 i).mstore 32 4).machine_state
      = ((σ.mstore 0 i).mstore 32 4).machine_state := by
    show ((σ.sstore a v).machine_state.updateMemory 0 i).updateMemory 32 4
      = (σ.machine_state.updateMemory 0 i).updateMemory 32 4
    rw [machine_state_sstore']
  have hkm : (((σ.sstore a v).mstore 0 i).mstore 32 4).keccak_map
      = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore, keccak_map_sstore']
  have hkm0 : ((σ.mstore 0 i).mstore 32 4).keccak_map = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore]
  have hc' : Finmap.lookup
      (mkInterval ((σ.mstore 0 i).mstore 32 4).machine_state 0 64)
      σ.keccak_map = some w := hc
  rw [keccakOut_fst_cached (by rw [hms, hkm]; exact hc'),
      keccakOut_fst_cached (by rw [hkm0]; exact hc')]

/-- **Leaf decoding is `sstore`-invariant outside the leaf's two abstract
field slots** (cached mapping hash; the write may target other leaves, the
count, or any node array). -/
theorem decodeLeaf_sstore_outside {σ : EVMState} {a v i w : UInt256}
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
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
    (hc : Finmap.lookup (accInterval σ key 4) σ.keccak_map = some w) :
    Finmap.lookup (accInterval (σ.sstore a v) key 4)
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
    (hc : Finmap.lookup (accInterval σ n 4) σ.keccak_map = some w) :
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
    (hc : Finmap.lookup (accInterval σ (σ.sload 1) 4) σ.keccak_map = some w)
    (hnw : (σ.sload 1).val + 1 < 2 ^ 256)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ wm, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some wm)
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
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w) :
    ((σ.mstore 0 i).mstore 32 4).keccak256 0 64
      = some (w, (σ.mstore 0 i).mstore 32 4)
    ∧ leafSlot σ i = w := by
  have hkm : ((σ.mstore 0 i).mstore 32 4).keccak_map = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore]
  constructor
  · exact keccak256_of_cached (by rw [hkm]; exact hc)
  · exact keccakOut_fst_cached (by rw [hkm]; exact hc)

/-- **Slot injectivity**: distinct cached keys live at distinct slots. -/
theorem leafSlot_inj {σ : EVMState} {i j wi wj : UInt256}
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi)
    (hcj : Finmap.lookup (accInterval σ j 4) σ.keccak_map = some wj)
    (hij : i ≠ j) : leafSlot σ i ≠ leafSlot σ j := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  obtain ⟨hkj, hvj⟩ := leafSlot_keccak hcj
  rw [hvi, hvj]
  exact Clear.KeccakInjective.keccak256_inj hki hkj (accInterval_ne hij)

/-- **Offset separation**: a small offset of one leaf slot never hits
another leaf's slot. -/
theorem leafSlot_add_ne {σ : EVMState} {i j wi wj k : UInt256}
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi)
    (hcj : Finmap.lookup (accInterval σ j 4) σ.keccak_map = some wj)
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
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi)
    (hcj : Finmap.lookup (accInterval σ j 4) σ.keccak_map = some wj)
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
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i ≠ c := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hc
  rw [hvi]
  exact Clear.KeccakInjective.keccak256_ne_lowSlot c hki hlow

/-- **Offset slots avoid the reserved low slots.** -/
theorem leafSlot_add_ne_low {σ : EVMState} {i w : UInt256} (k c : UInt256)
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i + k ≠ c := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hc
  rw [hvi]
  exact Clear.KeccakInjective.keccak256_add_ne_lowSlot k c hki hk hlow

/-! ### The clean insert agreement -/

/-- **INSERT AGREEMENT, clean form** — `leafSetOf_after_write` with every
slot-disjointness oracle discharged by the keccak-injectivity layer.  What
remains: the executing account exists, the count does not wrap, and the
mapping hashes of all indices `≤ count` are cached (the accessor caches on
first use). -/
theorem leafSetOf_insert {σ : EVMState} {v ni nv w : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hnw : (σ.sload 1).val + 1 < 2 ^ 256)
    (hc : Finmap.lookup (accInterval σ (σ.sload 1) 4) σ.keccak_map = some w)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ wm, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some wm) :
    leafSetOf ((((σ.sstore (leafSlot σ (σ.sload 1)) v).sstore
        (leafSlot σ (σ.sload 1) + 1) ni).sstore
        (leafSlot σ (σ.sload 1) + 2) nv).sstore 1 (σ.sload 1 + 1))
      = insert (⟨v, nv⟩ : AbsLeaf) (leafSetOf σ) := by
  have hkey : ∀ m : ℕ, m < (σ.sload 1).val → σ.sload 1 ≠ (m : UInt256) := by
    intro m hm
    apply Fin.ne_of_val_ne
    have hmv : ((m : UInt256)).val = m :=
      Nat.mod_eq_of_lt (lt_trans hm (σ.sload 1).isLt)
    rw [hmv]
    exact Nat.ne_of_gt hm
  refine leafSetOf_after_write hacc hc hnw hcaches ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨wm, hcm⟩ := hcaches m hm
    exact ⟨leafSlot_inj hc hcm (hkey m hm),
           Ne.symm (leafSlot_add_ne hcm hc (Ne.symm (hkey m hm)) (by decide))⟩
  · intro m hm
    obtain ⟨wm, hcm⟩ := hcaches m hm
    exact ⟨leafSlot_add_ne hc hcm (hkey m hm) (by decide),
           leafSlot_off_ne_off hc hcm (hkey m hm)
             (by decide) (by decide) (by decide)⟩
  · intro m hm
    obtain ⟨wm, hcm⟩ := hcaches m hm
    exact ⟨leafSlot_add_ne hc hcm (hkey m hm) (by decide),
           leafSlot_off_ne_off hc hcm (hkey m hm)
             (by decide) (by decide) (by decide)⟩
  · intro m hm
    obtain ⟨wm, hcm⟩ := hcaches m hm
    exact ⟨Ne.symm (leafSlot_ne_low 1 hcm (by decide)),
           Ne.symm (leafSlot_add_ne_low 2 1 hcm (by decide) (by decide))⟩
  · exact Ne.symm (leafSlot_ne_low 1 hc (by decide))
  · exact Ne.symm (leafSlot_add_ne_low 2 1 hc (by decide) (by decide))

/-! ### Node-array separation: array-element slots never hit leaf slots

`padWalk`/`updateWalk` write only node-array elements (`arrOut`-derived
slots, 32-byte preimages) and reserved low slots; leaf structs live at
64-byte-preimage slots.  `mkInterval_ne_of_len_ne` (32 ≠ 64) plus the
slot-separation axiom keep the two families disjoint at any small offsets. -/

/-- The cached-hash success witness for an array data slot. -/
private lemma arrOut_keccak {σ : EVMState} {a w : UInt256}
    (hc : Finmap.lookup (mkInterval (σ.mstore 0 a).machine_state 0 32)
        σ.keccak_map = some w) :
    (σ.mstore 0 a).keccak256 0 32 = some (w, σ.mstore 0 a)
    ∧ (arrOut σ a).1 = w := by
  have hkm : (σ.mstore 0 a).keccak_map = σ.keccak_map := keccak_map_mstore σ 0 a
  constructor
  · exact keccak256_of_cached (by rw [hkm]; exact hc)
  · unfold arrOut
    exact keccakOut_fst_cached (by rw [hkm]; exact hc)

/-- **General two-sided keccak offset separation**: hashes of distinct
preimages stay distinct under any two small offsets (either order). -/
private lemma keccak_off_ne_off
    {σ₁ σ₂ σ₁' σ₂' : EVMState} {p₁ n₁ p₂ n₂ r₁ r₂ k₁ k₂ : UInt256}
    (hk1 : σ₁.keccak256 p₁ n₁ = some (r₁, σ₁'))
    (hk2 : σ₂.keccak256 p₂ n₂ = some (r₂, σ₂'))
    (hne : mkInterval σ₁.machine_state p₁ n₁ ≠ mkInterval σ₂.machine_state p₂ n₂)
    (hs₁ : k₁.val < Clear.KeccakInjective.lowSlotBound)
    (hs₂ : k₂.val < Clear.KeccakInjective.lowSlotBound) :
    r₁ + k₁ ≠ r₂ + k₂ := by
  rcases Nat.le_total k₁.val k₂.val with hle | hle
  all_goals intro heq
  · -- k₁ ≤ k₂ : cancel k₁, offset (k₂ − k₁) on the r₂ side
    have hd : ((k₂.val - k₁.val : ℕ) : UInt256).val = k₂.val - k₁.val := by
      apply Nat.mod_eq_of_lt
      calc k₂.val - k₁.val ≤ k₂.val := Nat.sub_le _ _
      _ < UInt256.size := k₂.isLt
    have hk2eq : k₁ + ((k₂.val - k₁.val : ℕ) : UInt256) = k₂ := by
      apply Fin.ext
      show (k₁.val + ((k₂.val - k₁.val : ℕ) : UInt256).val) % UInt256.size = k₂.val
      rw [hd, Nat.add_sub_cancel' hle]
      exact Nat.mod_eq_of_lt k₂.isLt
    have heq' : r₁ + k₁ = (r₂ + ((k₂.val - k₁.val : ℕ) : UInt256)) + k₁ := by
      rw [heq]
      conv_lhs => rw [← hk2eq]
      ring
    have hcore : r₁ = r₂ + ((k₂.val - k₁.val : ℕ) : UInt256) :=
      add_right_cancel heq'
    exact Clear.KeccakInjective.keccak256_slot_sep hk2 hk1 (Ne.symm hne)
      (by rw [hd]; exact lt_of_le_of_lt (Nat.sub_le _ _) hs₂) hcore.symm
  · -- k₂ ≤ k₁ : symmetric
    have hd : ((k₁.val - k₂.val : ℕ) : UInt256).val = k₁.val - k₂.val := by
      apply Nat.mod_eq_of_lt
      calc k₁.val - k₂.val ≤ k₁.val := Nat.sub_le _ _
      _ < UInt256.size := k₁.isLt
    have hk1eq : k₂ + ((k₁.val - k₂.val : ℕ) : UInt256) = k₁ := by
      apply Fin.ext
      show (k₂.val + ((k₁.val - k₂.val : ℕ) : UInt256).val) % UInt256.size = k₁.val
      rw [hd, Nat.add_sub_cancel' hle]
      exact Nat.mod_eq_of_lt k₁.isLt
    have heq' : (r₁ + ((k₁.val - k₂.val : ℕ) : UInt256)) + k₂ = r₂ + k₂ := by
      rw [← heq]
      conv_rhs => rw [← hk1eq]
      ring
    have hcore : r₁ + ((k₁.val - k₂.val : ℕ) : UInt256) = r₂ :=
      add_right_cancel heq'
    exact Clear.KeccakInjective.keccak256_slot_sep hk1 hk2 hne
      (by rw [hd]; exact lt_of_le_of_lt (Nat.sub_le _ _) hs₁) hcore

/-- **A node-array element never hits a leaf-field slot** (any small element
index vs the `+0/+2` struct offsets — the preimage lengths differ, 32 vs 64). -/
theorem arr_elem_ne_leafSlot_add
    {σₐ σ : EVMState} {a j i k wa w : UInt256}
    (hca : Finmap.lookup (mkInterval (σₐ.mstore 0 a).machine_state 0 32)
        σₐ.keccak_map = some wa)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound) :
    (arrOut σₐ a).1 + j ≠ leafSlot σ i + k := by
  obtain ⟨hka, hva⟩ := arrOut_keccak hca
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  rw [hva, hvi]
  exact keccak_off_ne_off hka hki
    (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide))
    hj hk

/-- **Leaf decoding survives a node-array write.** -/
theorem decodeLeaf_arrWrite
    {σₐ σ : EVMState} {a j i v wa w : UInt256}
    (hca : Finmap.lookup (mkInterval (σ.mstore 0 a).machine_state 0 32)
        σ.keccak_map = some wa)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound) :
    decodeLeaf (σ.sstore ((arrOut σ a).1 + j) v) i = decodeLeaf σ i := by
  refine decodeLeaf_sstore_outside hci ?_ ?_
  · have := arr_elem_ne_leafSlot_add (σₐ := σ) (σ := σ)
      (k := 0) hca hci hj (by decide)
    simpa using this
  · exact arr_elem_ne_leafSlot_add (σₐ := σ) (σ := σ) hca hci hj (by decide)

/-! ### Cross-state transport (the junk-window discipline)

The walk steps bump the free pointer (bytes `[64, 95)`), and the keccak
model's junk window makes every accessor preimage depend on those bytes —
leaf slots can DRIFT across a walk.  As everywhere in this corpus
(cf. `read_after_mark_two`), the composition therefore transports
`decodeLeaf` across states with `accOut_deterministic`'s pack: junk-window
frame + cache monotonicity + cleanliness, plus `sload` agreement at the two
field slots. -/

/-- Any cached interval survives any `keccakOut` call: the cached branch
leaves the map alone, the fresh branch inserts at a key whose lookup was
`none` (≠ ours), and the collision branch only sets the flag. -/
private lemma cached_after_keccakOut {σ : EVMState} {p n : UInt256}
    {I : List UInt256} {w : UInt256}
    (h : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (keccakOut σ p n).2.keccak_map = some w := by
  unfold keccakOut EVMState.keccak256
  rcases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with _ | val
  · -- cache miss: fresh branch or collision
    simp only [hl]
    rcases hp : σ.keccak_range.partition (fun x => x ∈ σ.used_range) with ⟨unused, rest⟩
    rcases rest with _ | ⟨r, rs⟩
    · simpa [EVMState.addHashCollision] using h
    · simp only
      have hne : I ≠ mkInterval σ.machine_state p n := by
        intro heq
        rw [heq, hl] at h
        exact Option.noConfusion h
      rw [Finmap.lookup_insert_of_ne _ hne]
      exact h
  · -- cached: the map is untouched
    simp only [hl]
    exact h

/-- **`decodeLeaf` transport across states**: junk-window frame + cache
monotonicity + cleanliness pin the slot; `sload` agreement at the two field
slots pins the fields. -/
theorem decodeLeaf_deterministic {σ₁ σ₂ : EVMState} {i : UInt256}
    (hframe : ∀ b : UInt256, 64 ≤ b.val → b.val ≤ 94 →
      Finmap.lookup b σ₁.machine_state.memory
        = Finmap.lookup b σ₂.machine_state.memory)
    (hmono : ∀ w : UInt256,
      Finmap.lookup (accInterval σ₁ i 4) (accOut σ₁ i 4).2.keccak_map = some w →
        Finmap.lookup (accInterval σ₁ i 4) σ₂.keccak_map = some w)
    (hclean : (accOut σ₁ i 4).2.hash_collision = false)
    (hs0 : σ₂.sload (leafSlot σ₁ i) = σ₁.sload (leafSlot σ₁ i))
    (hs2 : σ₂.sload (leafSlot σ₁ i + 2) = σ₁.sload (leafSlot σ₁ i + 2)) :
    decodeLeaf σ₂ i = decodeLeaf σ₁ i := by
  have hslot : leafSlot σ₂ i = leafSlot σ₁ i := by
    show (accOut σ₂ i 4).1 = (accOut σ₁ i 4).1
    exact accOut_deterministic hframe hmono hclean
  unfold decodeLeaf
  rw [hslot, hs0, hs2]

/-! ### The retarget write (the other half of `imtInsert`) -/

/-- **RETARGET AGREEMENT**: writing `v` into the `nextValue` field of leaf
`idx` retargets exactly the abstract `nextKey` — the `value` field survives
(the two field slots differ by group arithmetic), the slot is
cache-stable. -/
theorem decodeLeaf_retarget {σ : EVMState} {idx v w : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hc : Finmap.lookup (accInterval σ idx 4) σ.keccak_map = some w) :
    decodeLeaf (σ.sstore (leafSlot σ idx + 2) v) idx
      = ⟨(decodeLeaf σ idx).key, v⟩ := by
  unfold decodeLeaf
  rw [leafSlot_sstore hc]
  rw [sload_sstore_ne (add_k_ne_self (by decide))]
  rw [sload_sstore_self hacc]

/-- **Retarget frame**: every other cached leaf decodes unchanged. -/
theorem decodeLeaf_retarget_outside {σ : EVMState} {idx i v w wi : UInt256}
    (hc : Finmap.lookup (accInterval σ idx 4) σ.keccak_map = some w)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi)
    (hne : idx ≠ i) :
    decodeLeaf (σ.sstore (leafSlot σ idx + 2) v) i = decodeLeaf σ i := by
  refine decodeLeaf_sstore_outside hci ?_ ?_
  · exact leafSlot_add_ne hc hci hne (by decide)
  · exact leafSlot_off_ne_off hc hci hne (by decide) (by decide) (by decide)

/-- **Retarget count frame**: the count survives (field slots avoid slot 1). -/
theorem leafCount_retarget {σ : EVMState} {idx v w : UInt256}
    (hc : Finmap.lookup (accInterval σ idx 4) σ.keccak_map = some w) :
    (σ.sstore (leafSlot σ idx + 2) v).sload 1 = σ.sload 1 :=
  sload_sstore_ne (leafSlot_add_ne_low 2 1 hc (by decide) (by decide))

/-! ### The pure image-update lemma -/

/-- Updating an injective enumeration at one index turns the image into an
erase-plus-insert — the set form of the retarget write. -/
private lemma image_update_erase_insert
    {f g : ℕ → AbsLeaf} {c a : ℕ} {B : AbsLeaf}
    (ha : a < c)
    (hagree : ∀ m, m < c → m ≠ a → g m = f m)
    (hga : g a = B)
    (hinj : ∀ m, m < c → ∀ m', m' < c → f m = f m' → m = m') :
    (Finset.range c).image g
      = insert B (((Finset.range c).image f).erase (f a)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase,
             Finset.mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩
    by_cases hma : m = a
    · left; rw [hma, hga]
    · right
      refine ⟨?_, m, hm, (hagree m hm hma).symm ▸ rfl⟩
      rw [hagree m hm hma]
      intro heq
      exact hma (hinj m hm a ha heq)
  · rintro (rfl | ⟨hne, m, hm, rfl⟩)
    · exact ⟨a, ha, hga⟩
    · refine ⟨m, hm, ?_⟩
      have hma : m ≠ a := fun h => hne (by rw [h])
      exact hagree m hm hma

/-! ### THE FIDELITY THEOREM: the glue sequence IS `imtInsert` -/

/-- The retarget write, named. -/
@[reducible] def retargetEvm (σ : EVMState) (widx v : UInt256) : EVMState :=
  σ.sstore (leafSlot σ widx + 2) v

/-- **THE STORAGE-SIDE `imtInsert`** — the AFM insert glue's leaves-mapping
write sequence (retarget the window leaf's `nextValue` to `v`, write the new
leaf struct `⟨v, ·, W₀.nextKey⟩` at the count, bump the count) produces
EXACTLY the abstract IMT insert:

`leafSetOf (…) = imtInsert (leafSetOf σ) (decodeLeaf σ widx) v`.

Hypotheses: account present; the window index is in range; the count does
not wrap; the window/count/all-lower mapping hashes are cached; and decoding
is injective below the count (the concrete shadow of the abstract `KeyInj`
invariant).  Everything else — slot separations, field survival, cache
transport — is discharged internally. -/
theorem leafSetOf_imtInsert {σ : EVMState} {widx v ni w wc : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hwlt : widx.val < (σ.sload 1).val)
    (hnw : (σ.sload 1).val + 1 < 2 ^ 256)
    (hcw : Finmap.lookup (accInterval σ widx 4) σ.keccak_map = some w)
    (hcc : Finmap.lookup (accInterval σ (σ.sload 1) 4) σ.keccak_map = some wc)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ wm, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some wm)
    (hinj : ∀ m : ℕ, m < (σ.sload 1).val → ∀ m' : ℕ, m' < (σ.sload 1).val →
      decodeLeaf σ (m : UInt256) = decodeLeaf σ (m' : UInt256) → m = m') :
    leafSetOf (((((retargetEvm σ widx v).sstore
        (leafSlot (retargetEvm σ widx v) ((retargetEvm σ widx v).sload 1)) v).sstore
        (leafSlot (retargetEvm σ widx v) ((retargetEvm σ widx v).sload 1) + 1) ni).sstore
        (leafSlot (retargetEvm σ widx v) ((retargetEvm σ widx v).sload 1) + 2)
          (decodeLeaf σ widx).nextKey).sstore
        1 ((retargetEvm σ widx v).sload 1 + 1))
      = imtInsert (leafSetOf σ) (decodeLeaf σ widx) v := by
  set σᵣ := retargetEvm σ widx v with hσᵣ
  have hcnt : σᵣ.sload 1 = σ.sload 1 := leafCount_retarget hcw
  -- Step A: the retarget write is erase-plus-insert
  have hstepA : leafSetOf σᵣ
      = insert (⟨(decodeLeaf σ widx).key, v⟩ : AbsLeaf)
          ((leafSetOf σ).erase (decodeLeaf σ widx)) := by
    unfold leafSetOf
    rw [hcnt]
    have hfa : decodeLeaf σ ((widx.val : ℕ) : UInt256) = decodeLeaf σ widx := by
      rw [Fin.cast_val_eq_self widx]
    rw [← hfa]
    refine image_update_erase_insert hwlt ?_ ?_ ?_
    · intro m hm hma
      obtain ⟨wm, hcm⟩ := hcaches m hm
      refine decodeLeaf_retarget_outside hcw hcm ?_
      intro heq
      apply hma
      have hmv : ((m : UInt256)).val = m :=
        Nat.mod_eq_of_lt (lt_trans hm (σ.sload 1).isLt)
      rw [← heq] at hmv
      exact hmv.symm
    · rw [Fin.cast_val_eq_self widx]
      exact decodeLeaf_retarget hacc hcw
    · exact hinj
  -- Step B: the struct write + bump is the set insert (over σᵣ)
  have haccr : (σᵣ.lookupAccount σᵣ.execution_env.code_owner).isSome :=
    acct_sstore hacc
  have hnwr : (σᵣ.sload 1).val + 1 < 2 ^ 256 := by rw [hcnt]; exact hnw
  have hccr : Finmap.lookup (accInterval σᵣ (σᵣ.sload 1) 4) σᵣ.keccak_map
      = some wc := by
    rw [hcnt, hσᵣ]
    exact cache_sstore hcc
  have hcachesr : ∀ m : ℕ, m < (σᵣ.sload 1).val →
      ∃ wm, Finmap.lookup (accInterval σᵣ (m : UInt256) 4) σᵣ.keccak_map
        = some wm := by
    rw [hcnt]
    intro m hm
    obtain ⟨wm, hcm⟩ := hcaches m hm
    exact ⟨wm, by rw [hσᵣ]; exact cache_sstore hcm⟩
  have hstepB := leafSetOf_insert (σ := σᵣ) (v := v) (ni := ni)
    (nv := (decodeLeaf σ widx).nextKey) haccr hnwr hccr hcachesr
  -- assemble
  rw [hstepB, hstepA]
  unfold imtInsert
  exact Finset.Insert.comm _ _ _

/-! ### The Evolution-step packaging -/

/-- **THE CONCRETE INSERT IS AN ABSTRACT `Evolution` STEP.**  With the
glue's own window guards (`W₀.key < v` and `nextKey = 0 ∨ v < nextKey` —
exactly what the insert's `require`s check), the storage write sequence
witnesses the insert disjunct of `IMTAbstract.Evolution`: some window leaf
in the current abstract set, a fresh key through its window, and the next
snapshot equal to `imtInsert`.  This is the exact step shape consumed by
`evolution_invariant`, `delivered_and_reclaimed_impossible` (#34) and
`delivered_leg_available_forever` (#60). -/
theorem leafSetOf_evolution_step {σ : EVMState} {widx v ni w wc : UInt256}
    (hacc : (σ.lookupAccount σ.execution_env.code_owner).isSome)
    (hwlt : widx.val < (σ.sload 1).val)
    (hnw : (σ.sload 1).val + 1 < 2 ^ 256)
    (hcw : Finmap.lookup (accInterval σ widx 4) σ.keccak_map = some w)
    (hcc : Finmap.lookup (accInterval σ (σ.sload 1) 4) σ.keccak_map = some wc)
    (hcaches : ∀ m : ℕ, m < (σ.sload 1).val →
      ∃ wm, Finmap.lookup (accInterval σ (m : UInt256) 4) σ.keccak_map = some wm)
    (hinj : ∀ m : ℕ, m < (σ.sload 1).val → ∀ m' : ℕ, m' < (σ.sload 1).val →
      decodeLeaf σ (m : UInt256) = decodeLeaf σ (m' : UInt256) → m = m')
    (hlow : (decodeLeaf σ widx).key < v)
    (hwin : (decodeLeaf σ widx).nextKey = 0 ∨ v < (decodeLeaf σ widx).nextKey) :
    ∃ W₀ v', W₀ ∈ leafSetOf σ ∧ W₀.key < v'
      ∧ (W₀.nextKey = 0 ∨ v' < W₀.nextKey)
      ∧ leafSetOf (((((retargetEvm σ widx v).sstore
          (leafSlot (retargetEvm σ widx v) ((retargetEvm σ widx v).sload 1)) v).sstore
          (leafSlot (retargetEvm σ widx v) ((retargetEvm σ widx v).sload 1) + 1) ni).sstore
          (leafSlot (retargetEvm σ widx v) ((retargetEvm σ widx v).sload 1) + 2)
            (decodeLeaf σ widx).nextKey).sstore
          1 ((retargetEvm σ widx v).sload 1 + 1))
        = imtInsert (leafSetOf σ) W₀ v' := by
  refine ⟨decodeLeaf σ widx, v, ?_, hlow, hwin,
    leafSetOf_imtInsert hacc hwlt hnw hcw hcc hcaches hinj⟩
  unfold leafSetOf
  exact Finset.mem_image.mpr
    ⟨widx.val, Finset.mem_range.mpr hwlt, by rw [Fin.cast_val_eq_self]⟩

/-! ### The valueToIndex family (base 5) and its separation from the leaves -/

/-- The `valueToIndex` slot: base slot 5 (`mapping_…_5196`,
`mapping_leaves_call`). -/
def vtiSlot (σ : EVMState) (v : UInt256) : UInt256 :=
  (accOut σ v 5).1

/-- The cached-hash success witness for a `valueToIndex` slot. -/
private lemma vtiSlot_keccak {σ : EVMState} {v w : UInt256}
    (hc : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some w) :
    ((σ.mstore 0 v).mstore 32 5).keccak256 0 64
      = some (w, (σ.mstore 0 v).mstore 32 5)
    ∧ vtiSlot σ v = w := by
  have hkm : ((σ.mstore 0 v).mstore 32 5).keccak_map = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore]
  constructor
  · exact keccak256_of_cached (by rw [hkm]; exact hc)
  · exact keccakOut_fst_cached (by rw [hkm]; exact hc)

/-- Base-4 and base-5 preimages differ at the word stored at address 32. -/
private lemma accInterval_base_ne {σ₁ σ₂ : EVMState} {x y : UInt256} :
    mkInterval ((σ₁.mstore 0 x).mstore 32 5).machine_state 0 64
      ≠ mkInterval ((σ₂.mstore 0 y).mstore 32 4).machine_state 0 64 := by
  apply Clear.KeccakInjective.mkInterval_0_64_ne_of_word32_ne
  have h5 : ((σ₁.mstore 0 x).mstore 32 5).machine_state.lookupMemory (32 : UInt256)
      = 5 := by
    have := Clear.KeccakInjective.mload_mstore_self (σ₁.mstore 0 x) 5
    unfold EVMState.mload at this
    exact this
  have h4 : ((σ₂.mstore 0 y).mstore 32 4).machine_state.lookupMemory (32 : UInt256)
      = 4 := by
    have := Clear.KeccakInjective.mload_mstore_self (σ₂.mstore 0 y) 4
    unfold EVMState.mload at this
    exact this
  rw [h5, h4]
  decide

/-- **The `valueToIndex` slot never hits a leaf-field slot** (base words 5
vs 4 make the preimages distinct at address 32). -/
theorem vtiSlot_ne_leafSlot_add {σ : EVMState} {v i k wv wi : UInt256}
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound) :
    vtiSlot σ v ≠ leafSlot σ i + k := by
  obtain ⟨hkv, hvv⟩ := vtiSlot_keccak hcv
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  rw [hvv, hvi]
  have hne := keccak_off_ne_off (k₁ := (0 : UInt256)) (k₂ := k)
    hkv hki accInterval_base_ne (by decide) hk
  intro heq
  exact hne (by simpa using heq)

/-- **Leaf decoding survives the `valueToIndex` write.** -/
theorem decodeLeaf_vtiWrite {σ : EVMState} {v u i wv wi : UInt256}
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi) :
    decodeLeaf (σ.sstore (vtiSlot σ v) u) i = decodeLeaf σ i := by
  refine decodeLeaf_sstore_outside hci ?_ ?_
  · have h0 : vtiSlot σ v ≠ leafSlot σ i + 0 :=
      vtiSlot_ne_leafSlot_add hcv hci (by decide)
    simpa using h0
  · exact vtiSlot_ne_leafSlot_add hcv hci (by decide)

/-- **The count survives the `valueToIndex` write.** -/
theorem leafCount_vtiWrite {σ : EVMState} {v u wv : UInt256}
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv) :
    (σ.sstore (vtiSlot σ v) u).sload 1 = σ.sload 1 := by
  obtain ⟨hkv, hvv⟩ := vtiSlot_keccak hcv
  refine sload_sstore_ne ?_
  rw [hvv]
  exact Clear.KeccakInjective.keccak256_ne_lowSlot 1 hkv (by decide)

/-! ### The accessor thread does not move the slot -/

/-- **Self-thread stability**: recomputing the leaf slot on the accessor's
own output state returns the same slot — the accessor caches its hash, its
scratch stays in `[0, 64)` (`accOut_junk_window`), and with `σ₂` the
accessor's own output the cache transport is the identity.  This is what
lets the glue's copy write (which runs on the threaded state) be read as a
write at `leafSlot` of the pre-accessor state. -/
theorem leafSlot_accThread {σ : EVMState} {i : UInt256}
    (hclean : (accOut σ i 4).2.hash_collision = false) :
    leafSlot (accOut σ i 4).2 i = leafSlot σ i := by
  show (accOut ((accOut σ i 4).2) i 4).1 = (accOut σ i 4).1
  refine accOut_deterministic ?_ (fun w hw => hw) hclean
  intro b hb1 _
  exact (accOut_junk_window hb1).symm

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
