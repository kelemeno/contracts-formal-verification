import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.IMTAbstract
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_replay_user
import specs.KeccakInjective
import specs.KeccakSlotSep
import specs.KeccakFresh
import specs.KeccakLowSlot

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

/-- The cached-hash success witness for a leaf slot (public: the weld file
pins guard-stage and final-state slots with it). -/
lemma leafSlot_keccak {σ : EVMState} {i w : UInt256}
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

/-- **Leaf slots avoid the reserved low slots — AXIOM-FREE.**  The window hypotheses are taken at `σ` and converted
through the accessor's two scratch writes: passing them at `σ` directly would make Lean unify `σ` with the
double-`mstore`d state, which does not terminate. -/
theorem leafSlot_ne_low_of_config {σ : EVMState} {i w : UInt256} (c : UInt256)
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) (hC : Clear.KeccakLowSlot.CachedInWindow σ)
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i ≠ c := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hc
  rw [hvi]
  exact Clear.KeccakLowSlot.keccak256_ne_lowSlot_of_config c
    (Clear.KeccakLowSlot.noLowInRange_of_window
      (Clear.KeccakLowSlot.rangeInWindow_mstore 32 4
        (Clear.KeccakLowSlot.rangeInWindow_mstore 0 i hR)))
    (Clear.KeccakLowSlot.noLowCached_of_window
      (Clear.KeccakLowSlot.cachedInWindow_mstore 32 4
        (Clear.KeccakLowSlot.cachedInWindow_mstore 0 i hC)))
    hki hlow

/-- **Offset leaf slots avoid the reserved low slots — AXIOM-FREE.** -/
theorem leafSlot_add_ne_low_of_config {σ : EVMState} {i w : UInt256} (k c : UInt256)
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) (hC : Clear.KeccakLowSlot.CachedInWindow σ)
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound) :
    leafSlot σ i + k ≠ c := by
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hc
  rw [hvi]
  exact Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config k c
    (Clear.KeccakLowSlot.rangeInWindow_mstore 32 4 (Clear.KeccakLowSlot.rangeInWindow_mstore 0 i hR))
    (Clear.KeccakLowSlot.cachedInWindow_mstore 32 4 (Clear.KeccakLowSlot.cachedInWindow_mstore 0 i hC))
    hki hk hlow

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
lemma arrOut_keccak {σ : EVMState} {a w : UInt256}
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

/-- **A node-array element never hits a leaf-field slot — AXIOM-FREE.**  As `arr_elem_ne_leafSlot_add`, but the
slot separation comes from `Clear.KeccakSlotSep.cached_off_ne_off` instead of the `keccak256_slot_sep`
idealization: both slots are cache hits, so `CacheInj` turns the preimages' inequality (lengths 32 vs 64) into the
slots', and `Separated` handles the two offsets.

Stated on a single state, which is how `decodeLeaf_arrWrite` calls it — `cached_off_ne_off` needs both hits in one
cache. -/
theorem arr_elem_ne_leafSlot_add_of_config {σ : EVMState} {a j i k wa w : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hca : Finmap.lookup (mkInterval (σ.mstore 0 a).machine_state 0 32)
        σ.keccak_map = some wa)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound) :
    (arrOut σ a).1 + j ≠ leafSlot σ i + k := by
  obtain ⟨-, hva⟩ := arrOut_keccak hca
  obtain ⟨-, hvi⟩ := leafSlot_keccak hci
  rw [hva, hvi]
  exact Clear.KeccakSlotSep.cached_off_ne_off hsep hinj hca hci
    (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hj hk

/-- **Leaf decoding survives a node-array write — AXIOM-FREE.** -/
theorem decodeLeaf_arrWrite_of_config
    {σ : EVMState} {a j i v wa w : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hca : Finmap.lookup (mkInterval (σ.mstore 0 a).machine_state 0 32)
        σ.keccak_map = some wa)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound) :
    decodeLeaf (σ.sstore ((arrOut σ a).1 + j) v) i = decodeLeaf σ i := by
  refine decodeLeaf_sstore_outside hci ?_ ?_
  · have := arr_elem_ne_leafSlot_add_of_config (k := 0) hsep hinj hca hci hj (by decide)
    simpa using this
  · exact arr_elem_ne_leafSlot_add_of_config hsep hinj hca hci hj (by decide)

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

/-- **The `valueToIndex` slot never hits a leaf-field slot — AXIOM-FREE.**  The preimages differ at address 32
(base words 5 vs 4), which `accInterval_base_ne` supplies; `CacheInj` turns that into slot distinctness and
`Separated` handles the offset. -/
theorem vtiSlot_ne_leafSlot_add_of_config {σ : EVMState} {v i k wv wi : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound) :
    vtiSlot σ v ≠ leafSlot σ i + k := by
  obtain ⟨-, hvv⟩ := vtiSlot_keccak hcv
  obtain ⟨-, hvi⟩ := leafSlot_keccak hci
  rw [hvv, hvi]
  have hne := Clear.KeccakSlotSep.cached_off_ne_off (k₁ := (0 : UInt256)) (k₂ := k)
    hsep hinj hcv hci accInterval_base_ne (by decide) hk
  intro heq
  exact hne (by simpa using heq)

/-- **Leaf decoding survives the `valueToIndex` write — AXIOM-FREE.** -/
theorem decodeLeaf_vtiWrite_of_config {σ : EVMState} {v u i wv wi : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv)
    (hci : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some wi) :
    decodeLeaf (σ.sstore (vtiSlot σ v) u) i = decodeLeaf σ i := by
  refine decodeLeaf_sstore_outside hci ?_ ?_
  · have h0 : vtiSlot σ v ≠ leafSlot σ i + 0 :=
      vtiSlot_ne_leafSlot_add_of_config hsep hinj hcv hci (by decide)
    simpa using h0
  · exact vtiSlot_ne_leafSlot_add_of_config hsep hinj hcv hci (by decide)

/-- **The count survives the `valueToIndex` write — AXIOM-FREE.** -/
theorem leafCount_vtiWrite_of_config {σ : EVMState} {v u wv : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) (hC : Clear.KeccakLowSlot.CachedInWindow σ)
    (hcv : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some wv) :
    (σ.sstore (vtiSlot σ v) u).sload 1 = σ.sload 1 := by
  obtain ⟨hkv, hvv⟩ := vtiSlot_keccak hcv
  refine sload_sstore_ne ?_
  rw [hvv]
  exact Clear.KeccakLowSlot.keccak256_ne_lowSlot_of_config 1
    (Clear.KeccakLowSlot.noLowInRange_of_window
      (Clear.KeccakLowSlot.rangeInWindow_mstore 32 5
        (Clear.KeccakLowSlot.rangeInWindow_mstore 0 v hR)))
    (Clear.KeccakLowSlot.noLowCached_of_window
      (Clear.KeccakLowSlot.cachedInWindow_mstore 32 5
        (Clear.KeccakLowSlot.cachedInWindow_mstore 0 v hC)))
    hkv (by decide)

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

/-- **Self-thread interval stability**: the accessor's own output computes
the SAME preimage interval (its scratch rewrites the same bytes, and the
junk window is untouched — `byte_double_mstore_eq` + `accOut_junk_window`).
Closes the `hcache` gap: the cached hash is cached AT the threaded state's
own interval. -/
theorem accInterval_accThread {σ : EVMState} {i : UInt256} :
    accInterval (accOut σ i 4).2 i 4 = accInterval σ i 4 := by
  unfold accInterval
  apply mkInterval_eq_of_byte_agree (by decide)
  intro b _ hb2
  have h0 : ((0 : UInt256)).val = 0 := rfl
  have h64 : ((64 : UInt256)).val = 64 := rfl
  rw [h0, h64] at hb2
  exact byte_double_mstore_eq (by omega)
    (fun h => accOut_junk_window h)

/-- The accessor's hash is cached at the threaded state's own interval. -/
theorem cached_accThread {σ : EVMState} {i : UInt256}
    (hclean : (accOut σ i 4).2.hash_collision = false) :
    Finmap.lookup (accInterval (accOut σ i 4).2 i 4)
        ((accOut σ i 4).2).keccak_map = some ((accOut σ i 4).1) := by
  rw [accInterval_accThread]
  exact accOut_caches_of_clean hclean

/-! ### The retarget-stage decode: the staged writes ARE the retargeted leaf -/

open Clear.KeccakDeterminism in
/-- **RETARGET-STAGE DECODE**: on the glue's staged state
(`retargetStageEvm` from `imt_insert_gate_user`; spelled out here to keep
the files decoupled), the window index decodes to exactly the retargeted
leaf `⟨lowLeaf.value, v⟩`: the copy's three writes land at the
thread-stable slot (`leafSlot_accThread` + `cached_accThread` +
`decodeLeaf_after_write`), and the field readbacks survive the accessor
scratch (`accOut_mload_high`) and resolve through the staging mstores. -/
theorem retargetStage_decode
    {evm : EVMState} {LM NI V IX : UInt256}
    (hclean : (accOut ((((evm.mstore 64 (evm.mload 64 + 96)).mstore
        (evm.mload 64) (evm.mload LM)).mstore
        (evm.mload 64 + 32) NI).mstore
        (evm.mload 64 + 64) V) IX 4).2.hash_collision = false)
    (hacc : (((accOut ((((evm.mstore 64 (evm.mload 64 + 96)).mstore
        (evm.mload 64) (evm.mload LM)).mstore
        (evm.mload 64 + 32) NI).mstore
        (evm.mload 64 + 64) V) IX 4).2).lookupAccount
        ((accOut ((((evm.mstore 64 (evm.mload 64 + 96)).mstore
        (evm.mload 64) (evm.mload LM)).mstore
        (evm.mload 64 + 32) NI).mstore
        (evm.mload 64 + 64) V) IX 4).2).execution_env.code_owner).isSome)
    (hplow : 96 ≤ (evm.mload 64).val)
    (hnw : (evm.mload 64).val + 128 ≤ 2 ^ 256) :
    decodeLeaf
      (let P := evm.mload 64
       let E4 := (((evm.mstore 64 (evm.mload 64 + 96)).mstore P (evm.mload LM)).mstore
           (P + 32) NI).mstore (P + 64) V
       let EK := (accOut E4 IX 4).2
       let SL := (accOut E4 IX 4).1
       ((EK.sstore SL (EK.mload P)).sstore
           (SL + 1) (EK.mload (P + 32))).sstore
           (SL + 2) (EK.mload (P + 64))) IX
      = ⟨evm.mload LM, V⟩ := by
  set P := evm.mload 64 with hP
  set E4 := (((evm.mstore 64 (P + 96)).mstore P (evm.mload LM)).mstore
      (P + 32) NI).mstore (P + 64) V with hE4
  set EK := (accOut E4 IX 4).2 with hEK
  have hsz : UInt256.size = 2 ^ 256 := by norm_num
  have hv64 : (P + 64).val = P.val + 64 := by
    show (P.val + ((64 : UInt256)).val) % UInt256.size = P.val + 64
    have : ((64 : UInt256)).val = 64 := rfl
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have hv32 : (P + 32).val = P.val + 32 := by
    show (P.val + ((32 : UInt256)).val) % UInt256.size = P.val + 32
    have : ((32 : UInt256)).val = 32 := rfl
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  -- field readbacks on the threaded state
  have hf2 : EK.mload (P + 64) = V := by
    rw [hEK]
    rw [accOut_mload_high (by rw [hv64]; omega) (by rw [hv64]; omega)]
    rw [hE4]
    exact mload_mstore_self_at _ _ _ (by rw [hv64]; omega)
  have hf0 : EK.mload P = evm.mload LM := by
    rw [hEK]
    rw [accOut_mload_high (by omega) (by omega)]
    rw [hE4]
    rw [mload_mstore_outside _ (P + 64) V P (by rw [hv64]; omega) (by omega)
      (Or.inl (by rw [hv64]; omega))]
    rw [mload_mstore_outside _ (P + 32) NI P (by rw [hv32]; omega) (by omega)
      (Or.inl (by rw [hv32]))]
    exact mload_mstore_self_at _ _ _ (by omega)
  -- the writes are at the thread-stable slot
  have hsl : leafSlot EK IX = (accOut E4 IX 4).1 := by
    rw [hEK, leafSlot_accThread hclean]
    rfl
  show decodeLeaf (((EK.sstore ((accOut E4 IX 4).1) (EK.mload P)).sstore
      ((accOut E4 IX 4).1 + 1) (EK.mload (P + 32))).sstore
      ((accOut E4 IX 4).1 + 2) (EK.mload (P + 64))) IX = ⟨evm.mload LM, V⟩
  rw [← hsl]
  rw [decodeLeaf_after_write hacc (cached_accThread hclean)]
  rw [hf0, hf2]

/-! ### Cross-accessor slot stability -/

/-- A cached interval survives an `accOut` step (any key, any base): the
accessor's scratch `mstore`s leave the cache untouched and its keccak call
preserves cached entries. -/
private lemma cached_after_accOut {σ : EVMState} {k b : UInt256}
    {I : List UInt256} {w : UInt256}
    (h : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (accOut σ k b).2.keccak_map = some w := by
  unfold Clear.KeccakDeterminism.accOut
  refine cached_after_keccakOut ?_
  rw [keccak_map_mstore, keccak_map_mstore]
  exact h

/-- **Cross-accessor slot frame**: a leaf slot whose hash is cached
survives ANY interleaved accessor step (the vti registration, other keys'
reads) — junk-window frame + cache survival + cleanliness. -/
theorem leafSlot_accOut_frame {σ : EVMState} {i k b w : UInt256}
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hclean : (accOut σ i 4).2.hash_collision = false) :
    leafSlot (accOut σ k b).2 i = leafSlot σ i := by
  show (accOut ((accOut σ k b).2) i 4).1 = (accOut σ i 4).1
  refine accOut_deterministic ?_ ?_ hclean
  · intro x hx1 _
    exact (accOut_junk_window hx1).symm
  · intro w' hw'
    -- the σ-side accessor's cached entry: transport hc through the k-thread
    have hcw : w' = w := by
      have h1 := cached_after_keccakOut (p := 0) (n := 64)
        (σ := (σ.mstore 0 i).mstore 32 4) (I := accInterval σ i 4) (w := w)
        (by rw [keccak_map_mstore, keccak_map_mstore]; exact hc)
      have h2 : (accOut σ i 4).2.keccak_map
          = (Clear.KeccakDeterminism.keccakOut ((σ.mstore 0 i).mstore 32 4) 0 64).2.keccak_map := rfl
      rw [h2] at hw'
      rw [h1] at hw'
      exact (Option.some.inj hw').symm
    rw [hcw]
    exact cached_after_accOut hc

/-- **Decode survives any accessor thread**: the slot is frame-stable and
accessors never write storage. -/
theorem decodeLeaf_accOut_frame {σ : EVMState} {i k b w : UInt256}
    (hc : Finmap.lookup (accInterval σ i 4) σ.keccak_map = some w)
    (hclean : (accOut σ i 4).2.hash_collision = false)
    (hcleanK : (accOut σ k b).2.hash_collision = false) :
    decodeLeaf (accOut σ k b).2 i = decodeLeaf σ i := by
  unfold decodeLeaf
  rw [leafSlot_accOut_frame hc hclean]
  rw [generated.L2InteropCommitmentTree.L2InteropCommitmentTree.sload_accOut_of_clean
      _ hcleanK,
    generated.L2InteropCommitmentTree.L2InteropCommitmentTree.sload_accOut_of_clean
      _ hcleanK]

/-- **Cross-accessor interval frame**: a later accessor's preimage interval
survives ANY interleaved accessor step (any key, any base) — the interleaved
step rewrites only its own scratch `[0, 64)` (which the re-scratch overwrites
identically on both sides) and its keccak call leaves memory alone, so the
junk window `[64, 95)` agrees (`accOut_junk_window`).  Generalizes
`accInterval_accThread` (the self-thread case) to arbitrary interleavings
(e.g. the vti registration between the copy and a leaf readback). -/
theorem accInterval_accOut_frame {σ : EVMState} {i k b : UInt256} :
    accInterval (accOut σ k b).2 i 4 = accInterval σ i 4 :=
  accInterval_eq (fun _ hx1 _ => accOut_junk_window hx1)

/-! ### The new-leaf stage decode: staging + copy + vti registration

The insert glue's new-leaf sequence: allocate the 96-byte struct at the free
pointer `P` (bump to `P + 96`), fill `{value := V, nextIndex := NI4,
nextValue := NV5}`, run the leaves accessor at `(IX1, 4)` (state `EK`, slot
`SL`), copy the three fields to storage (state `E5`), then run the
`valueToIndex` accessor at `(V, 5)` and write `IX1` at its slot.  The two
lemmas below are the two halves of the leaf-set bookkeeping: the staged
index decodes to the new abstract leaf, and every other cached index
decodes unchanged. -/

/-- `sstore` leaves the collision flag unchanged. -/
private lemma hash_collision_sstore' (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).hash_collision = σ.hash_collision := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- **NEW-LEAF-STAGE DECODE**: on the glue's fully staged new-leaf state,
index `IX1` decodes to exactly the new abstract leaf `⟨V, NV5⟩`: the copy
decodes as in `retargetStage_decode` (thread-stable slot via
`leafSlot_accThread`/`cached_accThread`, field readbacks over the accessor
scratch via `accOut_mload_high`, then `decodeLeaf_after_write`), the decode
survives the interleaved vti accessor thread (`decodeLeaf_accOut_frame` with
the cache transported through the three copy `sstore`s), and the final vti
write lands off the leaf fields (`vtiSlot_ne_leafSlot_add` at the threaded
state, the write slot pinned by `accOut_agree_value`). -/
theorem newLeafStage_decode
    {evm : EVMState} {V NI4 NV5 IX1 : UInt256} :
    let P := evm.mload 64
    let E4 := (((evm.mstore 64 (P + 96)).mstore P V).mstore
        (P + 32) NI4).mstore (P + 64) NV5
    let EK := (accOut E4 IX1 4).2
    let SL := (accOut E4 IX1 4).1
    let E5 := ((EK.sstore SL (EK.mload P)).sstore
        (SL + 1) (EK.mload (P + 32))).sstore (SL + 2) (EK.mload (P + 64))
    (accOut E4 IX1 4).2.hash_collision = false →
    (accOut E5 V 5).2.hash_collision = false →
    (EK.lookupAccount EK.execution_env.code_owner).isSome →
    96 ≤ P.val →
    P.val + 128 ≤ 2 ^ 256 →
    decodeLeaf ((accOut E5 V 5).2.sstore ((accOut E5 V 5).1) IX1) IX1
      = ⟨V, NV5⟩ := by
  intro P E4 EK SL E5 hclean4 hcleanV hacc hplow hnw
  have hE4 : E4 = (((evm.mstore 64 (P + 96)).mstore P V).mstore
      (P + 32) NI4).mstore (P + 64) NV5 := rfl
  have hEK : EK = (accOut E4 IX1 4).2 := rfl
  have hSL : SL = (accOut E4 IX1 4).1 := rfl
  have hE5 : E5 = ((EK.sstore SL (EK.mload P)).sstore
      (SL + 1) (EK.mload (P + 32))).sstore (SL + 2) (EK.mload (P + 64)) := rfl
  have hsz : UInt256.size = 2 ^ 256 := by norm_num
  have hv64 : (P + 64).val = P.val + 64 := by
    show (P.val + ((64 : UInt256)).val) % UInt256.size = P.val + 64
    have h64 : ((64 : UInt256)).val = 64 := rfl
    rw [h64]
    exact Nat.mod_eq_of_lt (by omega)
  have hv32 : (P + 32).val = P.val + 32 := by
    show (P.val + ((32 : UInt256)).val) % UInt256.size = P.val + 32
    have h32 : ((32 : UInt256)).val = 32 := rfl
    rw [h32]
    exact Nat.mod_eq_of_lt (by omega)
  -- field readbacks on the copy-accessor thread
  have hf2 : EK.mload (P + 64) = NV5 := by
    rw [hEK]
    rw [accOut_mload_high (by rw [hv64]; omega) (by rw [hv64]; omega)]
    rw [hE4]
    exact mload_mstore_self_at _ _ _ (by rw [hv64]; omega)
  have hf0 : EK.mload P = V := by
    rw [hEK]
    rw [accOut_mload_high (by omega) (by omega)]
    rw [hE4]
    rw [mload_mstore_outside _ (P + 64) NV5 P (by rw [hv64]; omega) (by omega)
      (Or.inl (by rw [hv64]; omega))]
    rw [mload_mstore_outside _ (P + 32) NI4 P (by rw [hv32]; omega) (by omega)
      (Or.inl (by rw [hv32]))]
    exact mload_mstore_self_at _ _ _ (by omega)
  -- the copy's writes land at the thread-stable slot
  have hcache : Finmap.lookup (accInterval EK IX1 4) EK.keccak_map = some SL := by
    rw [hEK, hSL]
    exact cached_accThread hclean4
  have hsl : leafSlot EK IX1 = SL := by
    rw [hEK, hSL]
    exact leafSlot_accThread hclean4
  -- (a) the copy decodes to the new leaf (the retargetStage_decode shape)
  have hcopy : decodeLeaf E5 IX1 = ⟨V, NV5⟩ := by
    have hwrite := decodeLeaf_after_write (σ := EK) (n := IX1)
      (v := EK.mload P) (ni := EK.mload (P + 32)) (nv := EK.mload (P + 64))
      hacc hcache
    rw [hsl] at hwrite
    rw [hE5, hwrite, hf0, hf2]
  -- (b) cache and cleanliness transport onto the copy-written state E5
  have hcacheE5 : Finmap.lookup (accInterval E5 IX1 4) E5.keccak_map
      = some SL := by
    rw [hE5]
    exact cache_sstore (cache_sstore (cache_sstore hcache))
  have hcollE5 : E5.hash_collision = false := by
    rw [hE5, hash_collision_sstore', hash_collision_sstore',
        hash_collision_sstore', hEK]
    exact hclean4
  have hcleanE5 : (accOut E5 IX1 4).2.hash_collision = false := by
    rw [accOut_of_cached hcacheE5]
    show ((E5.mstore 0 IX1).mstore 32 4).hash_collision = false
    rw [hash_collision_mstore, hash_collision_mstore]
    exact hcollE5
  -- the decode survives the vti accessor thread
  have hstep2 : decodeLeaf (accOut E5 V 5).2 IX1 = decodeLeaf E5 IX1 :=
    decodeLeaf_accOut_frame hcacheE5 hcleanE5 hcleanV
  -- the IX1 cache and the vti cache at the vti-threaded state
  have hcacheF : Finmap.lookup (accInterval (accOut E5 V 5).2 IX1 4)
      ((accOut E5 V 5).2).keccak_map = some SL := by
    rw [accInterval_accOut_frame]
    exact cached_after_accOut hcacheE5
  have hcvF : Finmap.lookup (accInterval (accOut E5 V 5).2 V 5)
      ((accOut E5 V 5).2).keccak_map = some ((accOut E5 V 5).1) := by
    rw [show accInterval (accOut E5 V 5).2 V 5 = accInterval E5 V 5 from
      accInterval_eq (fun _ hx1 _ => accOut_junk_window hx1)]
    exact accOut_caches_of_clean hcleanV
  -- the final vti write misses the leaf fields
  have hvti : vtiSlot (accOut E5 V 5).2 V = (accOut E5 V 5).1 := by
    show (accOut (accOut E5 V 5).2 V 5).1 = (accOut E5 V 5).1
    exact accOut_agree_value (fun _ hx1 _ => (accOut_junk_window hx1).symm)
      (accOut_caches_of_clean hcleanV)
  have hne0 : (accOut E5 V 5).1 ≠ leafSlot (accOut E5 V 5).2 IX1 := by
    have h := vtiSlot_ne_leafSlot_add (k := 0) hcvF hcacheF (by decide)
    rw [hvti] at h
    simpa using h
  have hne2 : (accOut E5 V 5).1 ≠ leafSlot (accOut E5 V 5).2 IX1 + 2 := by
    have h := vtiSlot_ne_leafSlot_add (k := 2) hcvF hcacheF (by decide)
    rw [hvti] at h
    exact h
  have hstep1 : decodeLeaf ((accOut E5 V 5).2.sstore ((accOut E5 V 5).1) IX1) IX1
      = decodeLeaf (accOut E5 V 5).2 IX1 :=
    decodeLeaf_sstore_outside hcacheF hne0 hne2
  rw [hstep1, hstep2, hcopy]

/-- **NEW-LEAF-STAGE FRAME (other indices)**: on the same staged state, every
OTHER cached index `m ≠ IX1` decodes unchanged.  ANCHOR NOTE: the frame is
against `E4` (the post-staging memory state), not the raw `evm` — the
free-pointer bump `mstore 64 (P + 96)` rewrites the junk window `[64, 95)`,
so the `m`-accessor preimage (and hence the slot) of `evm` and of the staged
chain need not agree; `E4`'s STORAGE is still `evm`'s (the staging `mstore`s
touch memory only), so `decodeLeaf E4 m` reads `evm`'s field values at the
staged-memory slot.  Transport chain, each step re-transporting the
`m`-cache (junk-window discipline): the copy accessor thread
(`decodeLeaf_accOut_frame` + `accInterval_accOut_frame`/`cached_after_accOut`),
the three copy `sstore`s (slot separations from
`leafSlot_inj`/`leafSlot_add_ne`/`leafSlot_off_ne_off` at the threaded
state, caches via `cache_sstore`), the vti accessor thread
(`decodeLeaf_accOut_frame` again), and the final vti write
(`vtiSlot_ne_leafSlot_add`, the write slot pinned by `accOut_agree_value`). -/
theorem decodeLeaf_stage_outside
    {evm : EVMState} {V NI4 NV5 IX1 m wm : UInt256} :
    let P := evm.mload 64
    let E4 := (((evm.mstore 64 (P + 96)).mstore P V).mstore
        (P + 32) NI4).mstore (P + 64) NV5
    let EK := (accOut E4 IX1 4).2
    let SL := (accOut E4 IX1 4).1
    let E5 := ((EK.sstore SL (EK.mload P)).sstore
        (SL + 1) (EK.mload (P + 32))).sstore (SL + 2) (EK.mload (P + 64))
    (accOut E4 IX1 4).2.hash_collision = false →
    (accOut E5 V 5).2.hash_collision = false →
    Finmap.lookup (accInterval E4 m 4) E4.keccak_map = some wm →
    (accOut E4 m 4).2.hash_collision = false →
    m ≠ IX1 →
    decodeLeaf ((accOut E5 V 5).2.sstore ((accOut E5 V 5).1) IX1) m
      = decodeLeaf E4 m := by
  intro P E4 EK SL E5 hclean4 hcleanV hcm hcleanm hmne
  have hEK : EK = (accOut E4 IX1 4).2 := rfl
  have hSL : SL = (accOut E4 IX1 4).1 := rfl
  have hE5 : E5 = ((EK.sstore SL (EK.mload P)).sstore
      (SL + 1) (EK.mload (P + 32))).sstore (SL + 2) (EK.mload (P + 64)) := rfl
  -- the two caches at the copy-threaded state EK
  have hcIX : Finmap.lookup (accInterval EK IX1 4) EK.keccak_map = some SL := by
    rw [hEK, hSL]
    exact cached_accThread hclean4
  have hcmEK : Finmap.lookup (accInterval EK m 4) EK.keccak_map = some wm := by
    rw [hEK, accInterval_accOut_frame]
    exact cached_after_accOut hcm
  have hsl : leafSlot EK IX1 = SL := by
    rw [hEK, hSL]
    exact leafSlot_accThread hclean4
  -- slot separations at EK (keccak injectivity, IX1 ≠ m)
  have hne : IX1 ≠ m := fun h => hmne h.symm
  have h00 : SL ≠ leafSlot EK m := by
    rw [← hsl]
    exact leafSlot_inj hcIX hcmEK hne
  have h02 : SL ≠ leafSlot EK m + 2 := by
    rw [← hsl]
    have h := leafSlot_off_ne_off (k₁ := 0) (k₂ := 2) hcIX hcmEK hne
      (by decide) (by decide) (by decide)
    simpa using h
  have h10 : SL + 1 ≠ leafSlot EK m := by
    rw [← hsl]
    exact leafSlot_add_ne hcIX hcmEK hne (by decide)
  have h12 : SL + 1 ≠ leafSlot EK m + 2 := by
    rw [← hsl]
    exact leafSlot_off_ne_off (k₁ := 1) (k₂ := 2) hcIX hcmEK hne
      (by decide) (by decide) (by decide)
  have h20 : SL + 2 ≠ leafSlot EK m := by
    rw [← hsl]
    exact leafSlot_add_ne hcIX hcmEK hne (by decide)
  have h22 : SL + 2 ≠ leafSlot EK m + 2 := by
    rw [← hsl]
    exact leafSlot_off_ne_off (k₁ := 2) (k₂ := 2) hcIX hcmEK hne
      (by decide) (by decide) (by decide)
  -- cache and slot transport through the three copy sstores
  have hcm1 : Finmap.lookup (accInterval (EK.sstore SL (EK.mload P)) m 4)
      (EK.sstore SL (EK.mload P)).keccak_map = some wm :=
    cache_sstore hcmEK
  have hcm2 : Finmap.lookup (accInterval ((EK.sstore SL (EK.mload P)).sstore
      (SL + 1) (EK.mload (P + 32))) m 4)
      ((EK.sstore SL (EK.mload P)).sstore
        (SL + 1) (EK.mload (P + 32))).keccak_map = some wm :=
    cache_sstore hcm1
  have hslm1 : leafSlot (EK.sstore SL (EK.mload P)) m = leafSlot EK m :=
    leafSlot_sstore hcmEK
  have hslm2 : leafSlot ((EK.sstore SL (EK.mload P)).sstore
      (SL + 1) (EK.mload (P + 32))) m = leafSlot EK m := by
    rw [leafSlot_sstore hcm1, hslm1]
  -- the decode survives the copy writes
  have hstep3 : decodeLeaf E5 m = decodeLeaf EK m := by
    have e3 : SL + 2 ≠ leafSlot ((EK.sstore SL (EK.mload P)).sstore
        (SL + 1) (EK.mload (P + 32))) m := by
      rw [hslm2]
      exact h20
    have e3' : SL + 2 ≠ leafSlot ((EK.sstore SL (EK.mload P)).sstore
        (SL + 1) (EK.mload (P + 32))) m + 2 := by
      rw [hslm2]
      exact h22
    have e2 : SL + 1 ≠ leafSlot (EK.sstore SL (EK.mload P)) m := by
      rw [hslm1]
      exact h10
    have e2' : SL + 1 ≠ leafSlot (EK.sstore SL (EK.mload P)) m + 2 := by
      rw [hslm1]
      exact h12
    rw [hE5, decodeLeaf_sstore_outside hcm2 e3 e3',
        decodeLeaf_sstore_outside hcm1 e2 e2',
        decodeLeaf_sstore_outside hcmEK h00 h02]
  -- E5-level cache and cleanliness for the vti thread
  have hcmE5 : Finmap.lookup (accInterval E5 m 4) E5.keccak_map = some wm := by
    rw [hE5]
    exact cache_sstore hcm2
  have hcollE5 : E5.hash_collision = false := by
    rw [hE5, hash_collision_sstore', hash_collision_sstore',
        hash_collision_sstore', hEK]
    exact hclean4
  have hcleanE5m : (accOut E5 m 4).2.hash_collision = false := by
    rw [accOut_of_cached hcmE5]
    show ((E5.mstore 0 m).mstore 32 4).hash_collision = false
    rw [hash_collision_mstore, hash_collision_mstore]
    exact hcollE5
  have hstep2 : decodeLeaf (accOut E5 V 5).2 m = decodeLeaf E5 m :=
    decodeLeaf_accOut_frame hcmE5 hcleanE5m hcleanV
  -- the m-cache and the vti cache at the vti-threaded state
  have hcmF : Finmap.lookup (accInterval (accOut E5 V 5).2 m 4)
      ((accOut E5 V 5).2).keccak_map = some wm := by
    rw [accInterval_accOut_frame]
    exact cached_after_accOut hcmE5
  have hcvF : Finmap.lookup (accInterval (accOut E5 V 5).2 V 5)
      ((accOut E5 V 5).2).keccak_map = some ((accOut E5 V 5).1) := by
    rw [show accInterval (accOut E5 V 5).2 V 5 = accInterval E5 V 5 from
      accInterval_eq (fun _ hx1 _ => accOut_junk_window hx1)]
    exact accOut_caches_of_clean hcleanV
  -- the vti write misses leaf m's fields
  have hvti : vtiSlot (accOut E5 V 5).2 V = (accOut E5 V 5).1 := by
    show (accOut (accOut E5 V 5).2 V 5).1 = (accOut E5 V 5).1
    exact accOut_agree_value (fun _ hx1 _ => (accOut_junk_window hx1).symm)
      (accOut_caches_of_clean hcleanV)
  have hv0 : (accOut E5 V 5).1 ≠ leafSlot (accOut E5 V 5).2 m := by
    have h := vtiSlot_ne_leafSlot_add (k := 0) hcvF hcmF (by decide)
    rw [hvti] at h
    simpa using h
  have hv2 : (accOut E5 V 5).1 ≠ leafSlot (accOut E5 V 5).2 m + 2 := by
    have h := vtiSlot_ne_leafSlot_add (k := 2) hcvF hcmF (by decide)
    rw [hvti] at h
    exact h
  have hstep1 : decodeLeaf ((accOut E5 V 5).2.sstore ((accOut E5 V 5).1) IX1) m
      = decodeLeaf (accOut E5 V 5).2 m :=
    decodeLeaf_sstore_outside hcmF hv0 hv2
  -- back across the copy accessor thread to the staged anchor E4
  have hstep4 : decodeLeaf EK m = decodeLeaf E4 m := by
    rw [hEK]
    exact decodeLeaf_accOut_frame hcm hcleanm hclean4
  rw [hstep1, hstep2, hstep3, hstep4]

/-! ### Walk and pad frames at the leaf-slot family (`decodeLeaf` invariance)

The Merkle walk (`updateWalk`) and the padding walk (`padWalk`) write storage
ONLY at node-array element slots — `arrOut`-derived hashes of 32-byte
preimages plus small offsets — while the leaf struct fields live at
`leafSlot σᵣ i + k`, hashes of 64-byte accessor preimages.  The two families
are disjoint (`keccak_off_ne_off`, 32 ≠ 64), so `decodeLeaf` is invariant
across both walks.  DESIGN: the leaf slots are pinned against a FIXED
reference state `σᵣ` whose accessor hash is cached (`keccak_off_ne_off`
happily compares keccak witnesses across unrelated states), so the per-step
hypotheses are exactly the existing low-slot discharge packs
(`StepLowOK`/`PadLowOK`) — the reference cache never needs re-transporting
along the walk. -/

set_option maxHeartbeats 4000000

/-- The keccak success witness of a clean `arrOut` step, `keccak256` form. -/
private lemma arrOut_pair {σ : EVMState} {a : UInt256}
    (h : (arrOut σ a).2.hash_collision = false) :
    (σ.mstore 0 a).keccak256 0 32 = some ((arrOut σ a).1, (arrOut σ a).2) := by
  have hksome := keccakOut_some_of_clean
    (σ := σ.mstore 0 a) (p := 0) (n := 32) (by exact h)
  rw [hksome]
  rfl

/-- Collision-flag monotonicity, backwards through `arrOut`. -/
private lemma arrOut_clean_bw {σ : EVMState} {a : UInt256}
    (h : (arrOut σ a).2.hash_collision = false) : σ.hash_collision = false := by
  have := keccakOut_clean_backward (σ := σ.mstore 0 a) (p := 0) (n := 32)
    (by exact h)
  rwa [hash_collision_mstore] at this

/-- **D1 — a `nodeStore` write preserves the leaf-slot family.**  The parent
store of one walk level lands at `keccak(levelArray) + j` (32-byte preimage,
small `j`); a leaf-field slot `leafSlot σᵣ i + k` (64-byte preimage, small
`k`, pinned at ANY reference state `σᵣ` with a cached accessor hash) is never
hit — the preimage lengths differ (`keccak_off_ne_off`, 32 ≠ 64). -/
lemma nodeStore_sload_leaf
    {σ σᵣ : EVMState} {base l j v i k w : UInt256}
    (hclean : (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).2.hash_collision = false)
    (hcleanA : (arrOut σ base).2.hash_collision = false)
    (hci : Finmap.lookup (accInterval σᵣ i 4) σᵣ.keccak_map = some w)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound) :
    (nodeStore σ base l j v).sload (leafSlot σᵣ i + k)
      = σ.sload (leafSlot σᵣ i + k) := by
  unfold nodeStore
  have hpair := arrOut_pair hclean
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  have hne : (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).1 + j
      ≠ leafSlot σᵣ i + k := by
    rw [hvi]
    exact keccak_off_ne_off hpair hki
      (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hj hk
  rw [sload_sstore_ne hne]
  rw [sload_arrOut_of_clean _ hclean]
  rw [sload_arrOut_of_clean _ hcleanA]

/-- **D2a — the odd step preserves the leaf-slot family.** -/
lemma stepOdd_sload_leaf
    {σ σᵣ : EVMState} {base i idx cur li k w : UInt256}
    (hci : Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hj : (Fin.shiftRight idx 1).val < Clear.KeccakInjective.lowSlotBound)
    (hfin : oddFinClean σ base i idx cur) :
    ((stepOdd σ base i idx cur).2).sload (leafSlot σᵣ li + k)
      = σ.sload (leafSlot σᵣ li + k) := by
  unfold oddFinClean at hfin
  have h4 := arrOut_clean_bw hfin
  have h3 := arrOut_clean_bw h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_bw h2
  show (nodeStore (accOut (sibRead σ base i (idx - 1)).2
      (sibRead σ base i (idx - 1)).1 cur).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).1).sload
        (leafSlot σᵣ li + k)
    = σ.sload (leafSlot σᵣ li + k)
  rw [nodeStore_sload_leaf hfin h4 hci hj hk]
  rw [sload_accOut_of_clean _ h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload (leafSlot σᵣ li + k)
    = σ.sload (leafSlot σᵣ li + k)
  rw [sload_arrOut_of_clean _ h2]
  rw [sload_arrOut_of_clean _ h1]

/-- **D2b — the even step preserves the leaf-slot family.** -/
lemma stepEven_sload_leaf
    {σ σᵣ : EVMState} {base i idx cur li k w : UInt256}
    (hci : Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hj : (Fin.shiftRight idx 1).val < Clear.KeccakInjective.lowSlotBound)
    (hfin : evenFinClean σ base i idx cur) :
    ((stepEven σ base i idx cur).2).sload (leafSlot σᵣ li + k)
      = σ.sload (leafSlot σᵣ li + k) := by
  unfold evenFinClean at hfin
  have h4 := arrOut_clean_bw hfin
  have h3 := arrOut_clean_bw h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_bw h2
  show (nodeStore (accOut (sibRead σ base i (idx + 1)).2 cur
      (sibRead σ base i (idx + 1)).1).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).1).sload
        (leafSlot σᵣ li + k)
    = σ.sload (leafSlot σᵣ li + k)
  rw [nodeStore_sload_leaf hfin h4 hci hj hk]
  rw [sload_accOut_of_clean _ h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload (leafSlot σᵣ li + k)
    = σ.sload (leafSlot σᵣ li + k)
  rw [sload_arrOut_of_clean _ h2]
  rw [sload_arrOut_of_clean _ h1]

/-- **D2c — the edge step preserves the leaf-slot family.** -/
lemma stepEdge_sload_leaf
    {σ σᵣ : EVMState} {ss base i idx cur li k w : UInt256}
    (hci : Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hj : (Fin.shiftRight idx 1).val < Clear.KeccakInjective.lowSlotBound)
    (hfin : edgeFinClean σ ss base i idx cur) :
    ((stepEdge σ ss base i idx cur).2).sload (leafSlot σᵣ li + k)
      = σ.sload (leafSlot σᵣ li + k) := by
  unfold edgeFinClean at hfin
  have h4 := arrOut_clean_bw hfin
  have h3 := arrOut_clean_bw h4
  have h2 := accOut_clean_backward h3
  show (nodeStore (accOut (sideRead σ (ss + 3) i).2 cur
      (sideRead σ (ss + 3) i).1).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).1).sload
        (leafSlot σᵣ li + k)
    = σ.sload (leafSlot σᵣ li + k)
  rw [nodeStore_sload_leaf hfin h4 hci hj hk]
  rw [sload_accOut_of_clean _ h3]
  show ((arrOut σ (ss + 3)).2).sload (leafSlot σᵣ li + k)
    = σ.sload (leafSlot σᵣ li + k)
  rw [sload_arrOut_of_clean _ h2]

/-- **D2 — one walk step preserves the leaf-slot family** (dispatched odd /
even / edge; per-step conditions = the low-slot pack `StepLowOK`). -/
lemma updateStep_sload_leaf
    {σ σᵣ : EVMState} {ss base i idx maxN cur li k w : UInt256}
    (hci : Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hok : StepLowOK ss base (σ, i, idx, maxN, cur)) :
    ((updateStep σ ss base i idx maxN cur).2).sload (leafSlot σᵣ li + k)
      = σ.sload (leafSlot σᵣ li + k) := by
  obtain ⟨hj, hflag⟩ := hok
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      rw [if_pos hpar, if_pos hedge] at hflag
      exact stepEdge_sload_leaf hci hk hj hflag
    · rw [if_pos hpar, if_neg hedge]
      rw [if_pos hpar, if_neg hedge] at hflag
      exact stepEven_sload_leaf hci hk hj hflag
  · rw [if_neg hpar]
    rw [if_neg hpar] at hflag
    exact stepOdd_sload_leaf hci hk hj hflag

/-- **D3 — THE WALK PRESERVES THE LEAF-SLOT FAMILY.**  The slots are pinned
at the fixed reference state `σᵣ` (cached accessor hash), so the per-step
conditions are exactly the low-slot pack — no per-step cache transport. -/
lemma updateWalk_sload_leaf :
    ∀ (kk : ℕ) {σ σᵣ : EVMState} {ss base i idx maxN cur li k w : UInt256},
    Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w →
    k.val < Clear.KeccakInjective.lowSlotBound →
    (∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i idx maxN cur)) →
    ((updateWalk ss base kk σ i idx maxN cur).1).sload (leafSlot σᵣ li + k)
      = σ.sload (leafSlot σᵣ li + k) := by
  intro kk
  induction kk with
  | zero =>
    intro σ σᵣ ss base i idx maxN cur li k w _ _ _
    rfl
  | succ kk ih =>
    intro σ σᵣ ss base i idx maxN cur li k w hci hk hok
    have h0 := hok 0 (by omega)
    simp only [updateWalk] at h0 ⊢
    rw [ih hci hk (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [updateWalk] using this)]
    exact updateStep_sload_leaf hci hk h0

/-- **D4 — `decodeLeaf` IS INVARIANT ACROSS THE MERKLE WALK.**  Junk-window
frame (`updateWalk_junk`) + cache transport (`updateWalk_lookup_mono`) pin
the slot through `decodeLeaf_deterministic`; D3 at offsets `0`/`2` pins the
two field reads.  Hypotheses: the accessor hash cached at the walk's start
state, the start state collision-free, and the low-slot step pack. -/
theorem decodeLeaf_updateWalk
    (kk : ℕ) {σ : EVMState} {ss base i0 idx maxN cur li w : UInt256}
    (hci : Finmap.lookup (accInterval σ li 4) σ.keccak_map = some w)
    (hσ : σ.hash_collision = false)
    (hok : ∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i0 idx maxN cur)) :
    decodeLeaf ((updateWalk ss base kk σ i0 idx maxN cur).1) li
      = decodeLeaf σ li := by
  have hclean : (accOut σ li 4).2.hash_collision = false := by
    rw [accOut_of_cached hci]
    show ((σ.mstore 0 li).mstore 32 4).hash_collision = false
    rw [hash_collision_mstore, hash_collision_mstore]
    exact hσ
  refine decodeLeaf_deterministic ?_ ?_ hclean ?_ ?_
  · intro b hb1 _
    exact (updateWalk_junk kk hb1).symm
  · intro w' hw'
    have hw'' : Finmap.lookup (accInterval σ li 4) σ.keccak_map = some w' := by
      rw [accOut_of_cached hci] at hw'
      exact hw'
    rw [Option.some.inj (hw''.symm.trans hci)]
    exact updateWalk_lookup_mono kk hci
  · have h0 := updateWalk_sload_leaf kk (k := 0) hci (by decide) hok
    simpa using h0
  · exact updateWalk_sload_leaf kk (k := 2) hci (by decide) hok

/-! ### The padding-walk analogs (D5) -/

/-- The scratch `mstore`s preserve the junk window (local copy). -/
private lemma mstore_junk_f {σ : EVMState} {a v : UInt256} {b : UInt256}
    (ha : a.val + 32 ≤ 64) (hb : 64 ≤ b.val) :
    Finmap.lookup b (σ.mstore a v).machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  apply lookup_updateMemory_outside_val
  · omega
  · right
    omega

/-- `arrOut` preserves the junk window (its scratch is `[0, 32)`). -/
private lemma arrOut_junk_f {σ : EVMState} {a : UInt256} {b : UInt256}
    (hb : 64 ≤ b.val) :
    Finmap.lookup b (arrOut σ a).2.machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  unfold arrOut
  rw [keccakOut_machine_state]
  exact mstore_junk_f (by rw [(by decide : ((0 : UInt256)).val = 0)]; omega) hb

/-- The array push preserves the junk window (one `arrOut` scratch, two
`sstore`s). -/
private lemma pushEvm_junk {σ : EVMState} {arr v : UInt256} {b : UInt256}
    (hb : 64 ≤ b.val) :
    Finmap.lookup b (pushEvm σ arr v).machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  unfold pushEvm
  rw [machine_state_sstore', arrOut_junk_f hb, machine_state_sstore']

/-- One padding step preserves the junk window. -/
lemma padStep_junk {σ : EVMState} {i : UInt256} {b : UInt256}
    (hb : 64 ≤ b.val) :
    Finmap.lookup b (padStep σ i).machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  unfold padStep
  rw [pushEvm_junk hb, arrOut_junk_f hb, arrOut_junk_f hb]

/-- **The padding walk preserves the junk window** (`updateWalk_junk` twin). -/
lemma padWalk_junk :
    ∀ (kk : ℕ) {σ : EVMState} {i om m : UInt256} {b : UInt256},
    64 ≤ b.val →
    Finmap.lookup b ((padWalk kk σ i om m).1).machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  intro kk
  induction kk with
  | zero =>
    intro σ i om m b _
    rfl
  | succ kk ih =>
    intro σ i om m b hb
    simp only [padWalk]
    rw [ih hb, padStep_junk hb]

/-- `arrOut` only grows the keccak cache (local copy). -/
private lemma arrOut_mono_f {σ : EVMState} {a : UInt256}
    {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (arrOut σ a).2.keccak_map = some w := by
  unfold arrOut
  apply keccakOut_lookup_mono
  rwa [keccak_map_mstore]

/-- The array push only grows the keccak cache. -/
private lemma pushEvm_lookup_mono {σ : EVMState} {arr v : UInt256}
    {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (pushEvm σ arr v).keccak_map = some w := by
  unfold pushEvm
  rw [keccak_map_sstore']
  exact arrOut_mono_f (by rw [keccak_map_sstore']; exact hI)

/-- One padding step only grows the keccak cache. -/
lemma padStep_lookup_mono {σ : EVMState} {i : UInt256}
    {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (padStep σ i).keccak_map = some w := by
  unfold padStep
  exact pushEvm_lookup_mono (arrOut_mono_f (arrOut_mono_f hI))

/-- **The padding walk only grows the keccak cache** (`updateWalk_lookup_mono`
twin). -/
lemma padWalk_lookup_mono :
    ∀ (kk : ℕ) {σ : EVMState} {i om m : UInt256} {I : List UInt256} {w : UInt256},
    Finmap.lookup I σ.keccak_map = some w →
    Finmap.lookup I ((padWalk kk σ i om m).1).keccak_map = some w := by
  intro kk
  induction kk with
  | zero =>
    intro σ _ _ _ I w hI
    exact hI
  | succ kk ih =>
    intro σ i om m I w hI
    simp only [padWalk]
    exact ih (padStep_lookup_mono hI)

/-- **D5a — the padding step preserves the leaf-slot family.**  Both of its
stores land at `keccak(32-byte preimage) + small` slots (the length-slot
write is itself an element write of the level-2 array), so neither hits a
leaf-field slot (`keccak_off_ne_off`, 32 ≠ 64). -/
lemma padStep_sload_leaf
    {σ σᵣ : EVMState} {i li k w : UInt256}
    (hci : Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (hi : i.val < Clear.KeccakInjective.lowSlotBound)
    (hlen : (((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i)).val
      < Clear.KeccakInjective.lowSlotBound)
    (hfin : padFinClean σ i) :
    ((padStep σ i).sload (leafSlot σᵣ li + k)) = σ.sload (leafSlot σᵣ li + k) := by
  unfold padFinClean at hfin
  have hE1 : (((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).hash_collision
        = false :=
    arrOut_clean_bw hfin
  have hB : ((arrOut (arrOut σ 2).2 3).2).hash_collision = false := by
    rwa [hash_collision_sstore'] at hE1
  have hA : ((arrOut σ 2).2).hash_collision = false := arrOut_clean_bw hB
  obtain ⟨hki, hvi⟩ := leafSlot_keccak hci
  have hpairFin := arrOut_pair hfin
  have hpairA := arrOut_pair hA
  have hne1 : (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
      ((arrOut σ 2).1 + i)).1
      + ((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i)
      ≠ leafSlot σᵣ li + k := by
    rw [hvi]
    exact keccak_off_ne_off hpairFin hki
      (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hlen hk
  have hne2 : (arrOut σ 2).1 + i ≠ leafSlot σᵣ li + k := by
    rw [hvi]
    exact keccak_off_ne_off hpairA hki
      (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hi hk
  show ((pushEvm (arrOut (arrOut σ 2).2 3).2 ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut (arrOut σ 2).2 3).1 + i))).sload
        (leafSlot σᵣ li + k))
    = σ.sload (leafSlot σᵣ li + k)
  unfold pushEvm
  rw [sload_sstore_ne hne1]
  rw [sload_arrOut_of_clean _ hfin]
  rw [sload_sstore_ne hne2]
  rw [sload_arrOut_of_clean _ hB]
  rw [sload_arrOut_of_clean _ hA]

/-- **D5b — THE PADDING WALK PRESERVES THE LEAF-SLOT FAMILY.** -/
lemma padWalk_sload_leaf :
    ∀ (kk : ℕ) {σ σᵣ : EVMState} {i om m li k w : UInt256},
    Finmap.lookup (accInterval σᵣ li 4) σᵣ.keccak_map = some w →
    k.val < Clear.KeccakInjective.lowSlotBound →
    (∀ j, j < kk → PadLowOK (padWalk j σ i om m)) →
    ((padWalk kk σ i om m).1).sload (leafSlot σᵣ li + k)
      = σ.sload (leafSlot σᵣ li + k) := by
  intro kk
  induction kk with
  | zero =>
    intro σ σᵣ i om m li k w _ _ _
    rfl
  | succ kk ih =>
    intro σ σᵣ i om m li k w hci hk hok
    have h0 := hok 0 (by omega)
    simp only [padWalk] at h0 ⊢
    rw [ih hci hk (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [padWalk] using this)]
    exact padStep_sload_leaf hci hk h0.1 h0.2.1 h0.2.2

/-- **D5 — `decodeLeaf` IS INVARIANT ACROSS THE PADDING WALK.**  The
`decodeLeaf_updateWalk` twin: junk-window frame (`padWalk_junk`) + cache
transport (`padWalk_lookup_mono`) + D5b at offsets `0`/`2`. -/
theorem decodeLeaf_padWalk
    (kk : ℕ) {σ : EVMState} {i0 om m li w : UInt256}
    (hci : Finmap.lookup (accInterval σ li 4) σ.keccak_map = some w)
    (hσ : σ.hash_collision = false)
    (hok : ∀ j, j < kk → PadLowOK (padWalk j σ i0 om m)) :
    decodeLeaf ((padWalk kk σ i0 om m).1) li = decodeLeaf σ li := by
  have hclean : (accOut σ li 4).2.hash_collision = false := by
    rw [accOut_of_cached hci]
    show ((σ.mstore 0 li).mstore 32 4).hash_collision = false
    rw [hash_collision_mstore, hash_collision_mstore]
    exact hσ
  refine decodeLeaf_deterministic ?_ ?_ hclean ?_ ?_
  · intro b hb1 _
    exact (padWalk_junk kk hb1).symm
  · intro w' hw'
    have hw'' : Finmap.lookup (accInterval σ li 4) σ.keccak_map = some w' := by
      rw [accOut_of_cached hci] at hw'
      exact hw'
    rw [Option.some.inj (hw''.symm.trans hci)]
    exact padWalk_lookup_mono kk hci
  · have h0 := padWalk_sload_leaf kk (k := 0) hci (by decide) hok
    simpa using h0
  · exact padWalk_sload_leaf kk (k := 2) hci (by decide) hok

/-- **Count-slot frame, walk**: the leaf count (slot 1) survives the Merkle
walk — `updateWalk_sload_low` at `s = 1` (1 is a low slot; no leaf-slot
reasoning needed). -/
theorem updateWalk_sload_one
    (kk : ℕ) {σ : EVMState} {ss base i idx maxN cur : UInt256}
    (hok : ∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i idx maxN cur)) :
    ((updateWalk ss base kk σ i idx maxN cur).1).sload 1 = σ.sload 1 :=
  updateWalk_sload_low kk (s := 1) (by decide) hok

/-- **Count-slot frame, pad**: the leaf count (slot 1) survives the padding
walk — `padWalk_sload_low` at `s = 1`. -/
theorem padWalk_sload_one
    (kk : ℕ) {σ : EVMState} {i om m : UInt256}
    (hok : ∀ j, j < kk → PadLowOK (padWalk j σ i om m)) :
    ((padWalk kk σ i om m).1).sload 1 = σ.sload 1 :=
  padWalk_sload_low kk (s := 1) (by decide) hok

/-! ### THE SEQUENCE-LEVEL CAPSTONE: the real glue write order IS `imtInsert`

`glueSeq_leafSetOf` composes the frame inventory above over the REAL insert
glue sequence (state chain spelled inline, mirroring the decode lemmas):

  σ₀ = `evm`  (post-guards anchor; storage = entry storage)
   │  retarget staging (allocator bump + 3 scratch writes)      [memory only]
  E4 ─ leaves accessor at (IX, 4) ⟶ EK, slot SL                 [keccak only]
   │  3-field copy (`sstore` at SL/+1/+2)                       [storage]
  S1 ─ Merkle walk #1 (`updateWalk`: node arrays + low slots)   [storage]
  S2 ─ new-leaf staging (bump + 3 scratch writes)               [memory only]
  F4 ─ leaves accessor at (NI, 4) ⟶ FK, slot SL2                [keccak only]
   │  3-field copy at SL2/+1/+2                                 [storage]
  F5 ─ vti accessor at (V, 5) + registration write              [storage]
  S3 ─ count bump (`sstore 1 (count+1)`)                        [storage]
  SB ─ padding walk (`padWalk`)                                 [storage]
  SP ─ level-0 leaf write (`leafWriteEvm`)                      [storage]
  SW ─ Merkle walk #2 (`updateWalk`)                            [storage]
  SF   (final)

ANCHOR DIAGRAM (the junk-window discipline).  The two allocator bumps
(`mstore 64`) rewrite the junk window `[64, 95)`, so the accessor preimage
interval of an index `n` takes exactly THREE values along the chain, pinned
at the three anchors `evm` / `E4` / `F4`:

  * `accInterval evm n 4` — valid on `[evm, E4)`;
  * `accInterval E4 n 4`  — valid on `[E4, F4)`: the copy `sstore`s, the
    accessor scratches and walk #1 preserve the window
    (`machine_state_sstore'` / `accOut_junk_window` / `updateWalk_junk`);
  * `accInterval F4 n 4`  — valid on `[F4, SF]`: the same frames plus
    `padWalk_junk` and the `arrOut` scratches of the leaf write.

The cache pack `hcach` therefore carries, for every index `n ≤ count`, ONE
hash word cached at ALL THREE anchor intervals — the concrete shadow of
"keccak is a function of the 64 preimage bytes", which the junk-window model
artifact would otherwise lose across the bumps.  With the slots so pinned
(`leafSlot evm n = leafSlot E4 n = leafSlot F4 n = wₙ`, and
`leafSlot SF n = wₙ` by the F4→SF junk frame + cache monotonicity), every
decode along the chain reads at the SAME two field slots `wₙ` / `wₙ + 2`,
and the per-index story reduces to `sload` frames:

  * `m < count`, `m ≠ IX`: no write hits `w_m`/`w_m + 2` — S1-copy slots by
    keccak injectivity at E4 (`keccak_off_ne_off` + `accInterval_ne`), the
    walks by D3/D5b pinned at E4, the S3 stage (copy #2 + vti) by
    `decodeLeaf_stage_outside` (anchored at F4, slots re-pinned to `w_m`),
    the bump by the low-slot axiom, the leaf write by the 32-vs-64 preimage
    separation ⟹ `decodeLeaf SF m = decodeLeaf evm m`;
  * `IX` (the window leaf): the S1 copy writes `⟨evm.mload LM, NI, V⟩` at
    `w`/+1/+2 (`retargetStage_decode`, slot re-pinned to `w`), everything
    downstream is a frame ⟹ `decodeLeaf SF IX = ⟨(decodeLeaf evm IX).key, V⟩`
    by the guard-phase read-back `hkey`;
  * `count` (the new leaf): the S3 copy writes `⟨V, NI4, NV5⟩` at `wc`/+1/+2
    (`newLeafStage_decode`; `NV5` is the oldNextValue read from the low leaf
    BEFORE the retarget — the `_5` value — and the read-back `hnv` ties it
    to `(decodeLeaf evm IX).nextKey`), downstream is a frame ⟹
    `decodeLeaf SF count = ⟨V, (decodeLeaf evm IX).nextKey⟩`;
  * the count: every non-bump write misses slot 1 (low-slot axioms +
    `updateWalk_sload_one`/`padWalk_sload_one`), the bump adds 1 ⟹
    `SF.sload 1 = count + 1`.

`range_succ` + `image_update_erase_insert` + `Insert.comm` assemble
`leafSetOf SF = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V`. -/

/-- The three-field struct copy over an accessor thread preserves any slot
separated from its three write slots (the shared S1/F5 copy frame). -/
private lemma copyChain_sload_ne {σ4 : EVMState} {I x y z t : UInt256}
    (hclean : (accOut σ4 I 4).2.hash_collision = false)
    (h0 : (accOut σ4 I 4).1 ≠ t)
    (h1 : (accOut σ4 I 4).1 + 1 ≠ t)
    (h2 : (accOut σ4 I 4).1 + 2 ≠ t) :
    ((((accOut σ4 I 4).2.sstore ((accOut σ4 I 4).1) x).sstore
        ((accOut σ4 I 4).1 + 1) y).sstore ((accOut σ4 I 4).1 + 2) z).sload t
      = σ4.sload t := by
  rw [sload_sstore_ne h2, sload_sstore_ne h1, sload_sstore_ne h0,
      sload_accOut_of_clean t hclean]

/-- The level-0 leaf write preserves any slot separated from its element
slot (two clean `arrOut` scratches + one `sstore`). -/
private lemma leafWrite_sload_ne {σ : EVMState} {ss idx leaf t : UInt256}
    (hA1 : (arrOut σ (ss + 2)).2.hash_collision = false)
    (hA2 : (arrOut (arrOut σ (ss + 2)).2 (arrOut σ (ss + 2)).1).2.hash_collision
      = false)
    (hne : (arrOut (arrOut σ (ss + 2)).2 (arrOut σ (ss + 2)).1).1 + idx ≠ t) :
    (leafWriteEvm σ ss idx leaf).sload t = σ.sload t := by
  unfold leafWriteEvm
  rw [sload_sstore_ne hne, sload_arrOut_of_clean t hA2,
      sload_arrOut_of_clean t hA1]

open Clear.KeccakDeterminism in
/-- **THE GLUE-SEQUENCE FIDELITY THEOREM** — the composed state the insert
closed form produces (retarget stage → walk #1 → new-leaf stage + vti →
count bump → padding walk → level-0 leaf write → walk #2) satisfies the
abstract set equation

`leafSetOf SF = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V`.

Hypotheses: window index in range, count does not wrap, the new index `NI`
is the count, the guard-phase read-backs (`hkey`/`hnv`), allocator bounds
per staging segment, cleanliness per accessor/`arrOut` scratch, account
presence at the three `sload_sstore_self` sites, the tri-anchor cache pack,
decode injectivity below the count, and the two walks' + pad's low-slot
packs.  See the anchor diagram above. -/
theorem glueSeq_leafSetOf
    {evm : EVMState} {LM NI V IX NI4 NV5 : UInt256}
    {ss₁ base₁ i₁ idx₁ maxN₁ cur₁ : UInt256} {kk₁ : ℕ}
    {ip om mp : UInt256} {kp : ℕ}
    {ssw nidx hl : UInt256}
    {ss₂ base₂ i₂ idx₂ maxN₂ cur₂ : UInt256} {kk₂ : ℕ} :
    let P1 := evm.mload 64
    let E4 := (((evm.mstore 64 (P1 + 96)).mstore P1 (evm.mload LM)).mstore
        (P1 + 32) NI).mstore (P1 + 64) V
    let EK := (accOut E4 IX 4).2
    let SL := (accOut E4 IX 4).1
    let S1 := ((EK.sstore SL (EK.mload P1)).sstore
        (SL + 1) (EK.mload (P1 + 32))).sstore (SL + 2) (EK.mload (P1 + 64))
    let S2 := (updateWalk ss₁ base₁ kk₁ S1 i₁ idx₁ maxN₁ cur₁).1
    let P2 := S2.mload 64
    let F4 := (((S2.mstore 64 (P2 + 96)).mstore P2 V).mstore
        (P2 + 32) NI4).mstore (P2 + 64) NV5
    let FK := (accOut F4 NI 4).2
    let SL2 := (accOut F4 NI 4).1
    let F5 := ((FK.sstore SL2 (FK.mload P2)).sstore
        (SL2 + 1) (FK.mload (P2 + 32))).sstore (SL2 + 2) (FK.mload (P2 + 64))
    let S3 := (accOut F5 V 5).2.sstore ((accOut F5 V 5).1) NI
    let SB := S3.sstore 1 (S3.sload 1 + 1)
    let SP := (padWalk kp SB ip om mp).1
    let SW := leafWriteEvm SP ssw nidx hl
    let SF := (updateWalk ss₂ base₂ kk₂ SW i₂ idx₂ maxN₂ cur₂).1
    -- window guard and count arithmetic
    IX.val < (evm.sload 1).val →
    (evm.sload 1).val + 1 < 2 ^ 256 →
    NI = evm.sload 1 →
    -- guard-phase read-backs binding the staged values to σ₀-decodes
    evm.mload LM = (decodeLeaf evm IX).key →
    NV5 = (decodeLeaf evm IX).nextKey →
    -- allocator bounds per staging segment
    96 ≤ P1.val → P1.val + 128 ≤ 2 ^ 256 →
    96 ≤ P2.val → P2.val + 128 ≤ 2 ^ 256 →
    -- cleanliness per accessor / arrOut scratch
    (accOut E4 IX 4).2.hash_collision = false →
    (accOut F4 NI 4).2.hash_collision = false →
    (accOut F5 V 5).2.hash_collision = false →
    (arrOut SP (ssw + 2)).2.hash_collision = false →
    (arrOut (arrOut SP (ssw + 2)).2 (arrOut SP (ssw + 2)).1).2.hash_collision
      = false →
    -- account presence where `sload_sstore_self` fires
    (EK.lookupAccount EK.execution_env.code_owner).isSome →
    (FK.lookupAccount FK.execution_env.code_owner).isSome →
    (S3.lookupAccount S3.execution_env.code_owner).isSome →
    -- the leaf write's element index is small
    nidx.val < Clear.KeccakInjective.lowSlotBound →
    -- the tri-anchor cache pack (see the anchor diagram)
    (∀ m : ℕ, m ≤ (evm.sload 1).val → ∃ wm,
      Finmap.lookup (accInterval evm (m : UInt256) 4) evm.keccak_map = some wm
      ∧ Finmap.lookup (accInterval E4 (m : UInt256) 4) E4.keccak_map = some wm
      ∧ Finmap.lookup (accInterval F4 (m : UInt256) 4) F4.keccak_map = some wm) →
    -- decode injectivity below the count at σ₀
    (∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m') →
    -- the walks' low-slot packs
    (∀ j, j < kk₁ →
      StepLowOK ss₁ base₁ (updateWalk ss₁ base₁ j S1 i₁ idx₁ maxN₁ cur₁)) →
    (∀ j, j < kp → PadLowOK (padWalk j SB ip om mp)) →
    (∀ j, j < kk₂ →
      StepLowOK ss₂ base₂ (updateWalk ss₂ base₂ j SW i₂ idx₂ maxN₂ cur₂)) →
    leafSetOf SF = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
  intro P1 E4 EK SL S1 S2 P2 F4 FK SL2 F5 S3 SB SP SW SF
  intro hwlt hnw hNI hkey hnv hplow1 hnw1 hplow2 hnw2
  intro hclean4 hcleanF hcleanV hcleanA1 hcleanA2 haccEK haccFK haccS3 hnidx
  intro hcach hinj hok₁ hokp hok₂
  -- definitional handles on the chain
  have hEKd : EK = (accOut E4 IX 4).2 := rfl
  have hSLd : SL = (accOut E4 IX 4).1 := rfl
  have hS1d : S1 = ((EK.sstore SL (EK.mload P1)).sstore
      (SL + 1) (EK.mload (P1 + 32))).sstore (SL + 2) (EK.mload (P1 + 64)) := rfl
  have hS2d : S2 = (updateWalk ss₁ base₁ kk₁ S1 i₁ idx₁ maxN₁ cur₁).1 := rfl
  have hFKd : FK = (accOut F4 NI 4).2 := rfl
  have hSL2d : SL2 = (accOut F4 NI 4).1 := rfl
  have hF5d : F5 = ((FK.sstore SL2 (FK.mload P2)).sstore
      (SL2 + 1) (FK.mload (P2 + 32))).sstore (SL2 + 2) (FK.mload (P2 + 64)) := rfl
  have hS3d : S3 = (accOut F5 V 5).2.sstore ((accOut F5 V 5).1) NI := rfl
  have hSBd : SB = S3.sstore 1 (S3.sload 1 + 1) := rfl
  have hSPd : SP = (padWalk kp SB ip om mp).1 := rfl
  have hSWd : SW = leafWriteEvm SP ssw nidx hl := rfl
  have hSFd : SF = (updateWalk ss₂ base₂ kk₂ SW i₂ idx₂ maxN₂ cur₂).1 := rfl
  -- the staging `mstore`s are storage-transparent
  have hE4s : ∀ t : UInt256, E4.sload t = evm.sload t := fun _ => rfl
  have hF4s : ∀ t : UInt256, F4.sload t = S2.sload t := fun _ => rfl
  -- casts
  have hIXcast : ((IX.val : ℕ) : UInt256) = IX := Fin.cast_val_eq_self IX
  have hccast : (((evm.sload 1).val : ℕ) : UInt256) = evm.sload 1 :=
    Fin.cast_val_eq_self (evm.sload 1)
  -- the anchor caches of the window index and the count
  obtain ⟨w, hw0, hw4, hwF⟩ := hcach IX.val (le_of_lt hwlt)
  rw [hIXcast] at hw0 hw4 hwF
  obtain ⟨wc, hc0, hc4, hcF⟩ := hcach (evm.sload 1).val (le_refl _)
  rw [hccast] at hc0 hc4 hcF
  clear hw0 hc0
  -- slot pinning at the anchors
  have hvw4 : leafSlot E4 IX = w := (leafSlot_keccak hw4).2
  have hkw4 := (leafSlot_keccak hw4).1
  have hvc4 : leafSlot E4 (evm.sload 1) = wc := (leafSlot_keccak hc4).2
  have hkcF := (leafSlot_keccak hcF).1
  have haccw : (accOut E4 IX 4).1 = w := hvw4
  have haccwc : (accOut F4 NI 4).1 = wc := by
    rw [hNI]
    exact (leafSlot_keccak hcF).2
  -- collision-flag backchain to the F4 anchor
  have hcolF4 : F4.hash_collision = false := accOut_clean_backward hcleanF
  -- ===== the count chain: SF.sload 1 = count + 1 =====
  have hcntS1 : S1.sload 1 = evm.sload 1 := by
    rw [hS1d, hEKd, hSLd]
    refine (copyChain_sload_ne hclean4 ?_ ?_ ?_).trans (hE4s 1)
    · rw [haccw]
      exact Clear.KeccakInjective.keccak256_ne_lowSlot 1 hkw4 (by decide)
    · rw [haccw]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 1 1 hkw4
        (by decide) (by decide)
    · rw [haccw]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 2 1 hkw4
        (by decide) (by decide)
  have hcntS2 : S2.sload 1 = evm.sload 1 := by
    rw [hS2d, updateWalk_sload_one kk₁ hok₁]
    exact hcntS1
  have hcntF5 : F5.sload 1 = evm.sload 1 := by
    rw [hF5d, hFKd, hSL2d]
    refine (copyChain_sload_ne hcleanF ?_ ?_ ?_).trans ((hF4s 1).trans hcntS2)
    · rw [haccwc]
      exact Clear.KeccakInjective.keccak256_ne_lowSlot 1 hkcF (by decide)
    · rw [haccwc]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 1 1 hkcF
        (by decide) (by decide)
    · rw [haccwc]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 2 1 hkcF
        (by decide) (by decide)
  -- the vti write slot, pinned to the accessor's own output
  have hcvF' : Finmap.lookup (accInterval (accOut F5 V 5).2 V 5)
      ((accOut F5 V 5).2).keccak_map = some ((accOut F5 V 5).1) := by
    rw [show accInterval (accOut F5 V 5).2 V 5 = accInterval F5 V 5 from
      accInterval_eq (fun _ hx1 _ => accOut_junk_window hx1)]
    exact accOut_caches_of_clean hcleanV
  have hvtiSlot : vtiSlot (accOut F5 V 5).2 V = (accOut F5 V 5).1 :=
    accOut_agree_value (fun _ hx1 _ => (accOut_junk_window hx1).symm)
      (accOut_caches_of_clean hcleanV)
  have hcntS3 : S3.sload 1 = evm.sload 1 := by
    rw [hS3d]
    have h := leafCount_vtiWrite (σ := (accOut F5 V 5).2) (v := V) (u := NI) hcvF'
    rw [hvtiSlot] at h
    rw [h, sload_accOut_of_clean 1 hcleanV]
    exact hcntF5
  have hcntSB : SB.sload 1 = evm.sload 1 + 1 := by
    rw [hSBd, sload_sstore_self haccS3, hcntS3]
  have hcntSP : SP.sload 1 = evm.sload 1 + 1 := by
    rw [hSPd, padWalk_sload_one kp hokp]
    exact hcntSB
  have hcntSW : SW.sload 1 = evm.sload 1 + 1 := by
    rw [hSWd]
    have hne : (arrOut (arrOut SP (ssw + 2)).2 (arrOut SP (ssw + 2)).1).1 + nidx
        ≠ (1 : UInt256) :=
      Clear.KeccakInjective.keccak256_add_ne_lowSlot nidx 1 (arrOut_pair hcleanA2)
        hnidx (by decide)
    rw [leafWrite_sload_ne hcleanA1 hcleanA2 hne]
    exact hcntSP
  have hcntSF : SF.sload 1 = evm.sload 1 + 1 := by
    rw [hSFd, updateWalk_sload_one kk₂ hok₂]
    exact hcntSW
  have hcval : (SF.sload 1).val = (evm.sload 1).val + 1 := by
    rw [hcntSF]
    show ((evm.sload 1).val + (1 : UInt256).val) % 2 ^ 256 = (evm.sload 1).val + 1
    have h1v : ((1 : UInt256)).val = 1 := rfl
    rw [h1v]
    exact Nat.mod_eq_of_lt hnw
  -- ===== junk-window frames (E4 → S1, F4 → S3, F4 → SF) =====
  have hjS1 : ∀ b : UInt256, 64 ≤ b.val →
      Finmap.lookup b S1.machine_state.memory
        = Finmap.lookup b E4.machine_state.memory := by
    intro b hb
    rw [hS1d, machine_state_sstore', machine_state_sstore', machine_state_sstore',
        hEKd, accOut_junk_window hb]
  have hjS3 : ∀ b : UInt256, 64 ≤ b.val →
      Finmap.lookup b S3.machine_state.memory
        = Finmap.lookup b F4.machine_state.memory := by
    intro b hb
    rw [hS3d, machine_state_sstore', accOut_junk_window hb, hF5d,
        machine_state_sstore', machine_state_sstore', machine_state_sstore',
        hFKd, accOut_junk_window hb]
  have hjSF : ∀ b : UInt256, 64 ≤ b.val →
      Finmap.lookup b SF.machine_state.memory
        = Finmap.lookup b F4.machine_state.memory := by
    intro b hb
    rw [hSFd, updateWalk_junk kk₂ hb, hSWd]
    unfold leafWriteEvm
    rw [machine_state_sstore', arrOut_junk_f hb, arrOut_junk_f hb,
        hSPd, padWalk_junk kp hb, hSBd, machine_state_sstore']
    exact hjS3 b hb
  have hIntS1 : ∀ i : UInt256, accInterval S1 i 4 = accInterval E4 i 4 :=
    fun _ => accInterval_eq (fun b hb1 _ => hjS1 b hb1)
  have hIntS3 : ∀ i : UInt256, accInterval S3 i 4 = accInterval F4 i 4 :=
    fun _ => accInterval_eq (fun b hb1 _ => hjS3 b hb1)
  have hIntSF : ∀ i : UInt256, accInterval SF i 4 = accInterval F4 i 4 :=
    fun _ => accInterval_eq (fun b hb1 _ => hjSF b hb1)
  -- ===== cache-monotonicity chains =====
  have hmonoS1 : ∀ (I : List UInt256) (u : UInt256),
      Finmap.lookup I E4.keccak_map = some u →
      Finmap.lookup I S1.keccak_map = some u := by
    intro I u hI
    rw [hS1d, keccak_map_sstore', keccak_map_sstore', keccak_map_sstore', hEKd]
    exact cached_after_accOut hI
  have hmonoS3 : ∀ (I : List UInt256) (u : UInt256),
      Finmap.lookup I F4.keccak_map = some u →
      Finmap.lookup I S3.keccak_map = some u := by
    intro I u hI
    rw [hS3d, keccak_map_sstore']
    refine cached_after_accOut ?_
    rw [hF5d, keccak_map_sstore', keccak_map_sstore', keccak_map_sstore', hFKd]
    exact cached_after_accOut hI
  have hmonoSF : ∀ (I : List UInt256) (u : UInt256),
      Finmap.lookup I F4.keccak_map = some u →
      Finmap.lookup I SF.keccak_map = some u := by
    intro I u hI
    rw [hSFd]
    refine updateWalk_lookup_mono kk₂ ?_
    rw [hSWd]
    unfold leafWriteEvm
    rw [keccak_map_sstore']
    refine arrOut_mono_f (arrOut_mono_f ?_)
    rw [hSPd]
    refine padWalk_lookup_mono kp ?_
    rw [hSBd, keccak_map_sstore']
    exact hmonoS3 I u hI
  -- final-state slot pinning (F4-anchored caches survive to SF)
  have hslotSF : ∀ n u : UInt256,
      Finmap.lookup (accInterval F4 n 4) F4.keccak_map = some u →
      leafSlot SF n = u := by
    intro n u hn
    have h : Finmap.lookup (accInterval SF n 4) SF.keccak_map = some u := by
      rw [hIntSF n]
      exact hmonoSF _ _ hn
    exact (leafSlot_keccak h).2
  -- ===== the S1 copy values (retargetStage_decode, slot re-pinned) =====
  have hdecS1 : decodeLeaf S1 IX = ⟨evm.mload LM, V⟩ :=
    retargetStage_decode (evm := evm) (LM := LM) (NI := NI) (V := V) (IX := IX)
      hclean4 haccEK hplow1 hnw1
  have hslotS1IX : leafSlot S1 IX = w := by
    have h : Finmap.lookup (accInterval S1 IX 4) S1.keccak_map = some w := by
      rw [hIntS1 IX]
      exact hmonoS1 _ _ hw4
    exact (leafSlot_keccak h).2
  have hS1fields : S1.sload w = evm.mload LM ∧ S1.sload (w + 2) = V := by
    have h := hdecS1
    unfold decodeLeaf at h
    rw [hslotS1IX] at h
    exact ⟨congrArg AbsLeaf.key h, congrArg AbsLeaf.nextKey h⟩
  -- ===== the S3 copy values (newLeafStage_decode, slot re-pinned) =====
  have hdecS3 : decodeLeaf S3 NI = ⟨V, NV5⟩ :=
    newLeafStage_decode (evm := S2) (V := V) (NI4 := NI4) (NV5 := NV5) (IX1 := NI)
      hcleanF hcleanV haccFK hplow2 hnw2
  have hslotS3NI : leafSlot S3 NI = wc := by
    have h : Finmap.lookup (accInterval S3 NI 4) S3.keccak_map = some wc := by
      rw [hIntS3 NI, hNI]
      exact hmonoS3 _ _ hcF
    exact (leafSlot_keccak h).2
  have hS3fields : S3.sload wc = V ∧ S3.sload (wc + 2) = NV5 := by
    have h := hdecS3
    unfold decodeLeaf at h
    rw [hslotS3NI] at h
    exact ⟨congrArg AbsLeaf.key h, congrArg AbsLeaf.nextKey h⟩
  -- ===== the S3 → SF tail frame at any E4-anchored leaf slot =====
  have htail : ∀ n u k : UInt256,
      Finmap.lookup (accInterval E4 n 4) E4.keccak_map = some u →
      k.val < Clear.KeccakInjective.lowSlotBound →
      SF.sload (leafSlot E4 n + k) = S3.sload (leafSlot E4 n + k) := by
    intro n u k hcE hk
    rw [hSFd, updateWalk_sload_leaf kk₂ hcE hk hok₂, hSWd]
    have hne : (arrOut (arrOut SP (ssw + 2)).2 (arrOut SP (ssw + 2)).1).1 + nidx
        ≠ leafSlot E4 n + k := by
      obtain ⟨hki, hvi⟩ := leafSlot_keccak hcE
      rw [hvi]
      exact keccak_off_ne_off (arrOut_pair hcleanA2) hki
        (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hnidx hk
    rw [leafWrite_sload_ne hcleanA1 hcleanA2 hne,
        hSPd, padWalk_sload_leaf kp hcE hk hokp,
        hSBd, sload_sstore_ne (Ne.symm (leafSlot_add_ne_low k 1 hcE hk (by decide)))]
  -- ===== the S2 → S3 middle frame for non-count indices =====
  have hmid : ∀ n u : UInt256,
      Finmap.lookup (accInterval F4 n 4) F4.keccak_map = some u →
      n ≠ NI →
      S3.sload u = S2.sload u ∧ S3.sload (u + 2) = S2.sload (u + 2) := by
    intro n u hcFn hne
    have hcleann : (accOut F4 n 4).2.hash_collision = false := by
      rw [accOut_of_cached hcFn]
      show ((F4.mstore 0 n).mstore 32 4).hash_collision = false
      rw [hash_collision_mstore, hash_collision_mstore]
      exact hcolF4
    have hdec : decodeLeaf S3 n = decodeLeaf F4 n :=
      decodeLeaf_stage_outside (evm := S2) (V := V) (NI4 := NI4) (NV5 := NV5)
        (IX1 := NI) (m := n) (wm := u) hcleanF hcleanV hcFn hcleann hne
    have hsS3 : leafSlot S3 n = u := by
      have h : Finmap.lookup (accInterval S3 n 4) S3.keccak_map = some u := by
        rw [hIntS3 n]
        exact hmonoS3 _ _ hcFn
      exact (leafSlot_keccak h).2
    have hsF4 : leafSlot F4 n = u := (leafSlot_keccak hcFn).2
    unfold decodeLeaf at hdec
    rw [hsS3, hsF4] at hdec
    exact ⟨(congrArg AbsLeaf.key hdec).trans (hF4s u),
           (congrArg AbsLeaf.nextKey hdec).trans (hF4s (u + 2))⟩
  -- ===== per-index: below-count, non-window =====
  have houtside : ∀ m : ℕ, m < (evm.sload 1).val → m ≠ IX.val →
      decodeLeaf SF (m : UInt256) = decodeLeaf evm (m : UInt256) := by
    intro m hm hmIX
    obtain ⟨wm, hm0, hm4, hmF⟩ := hcach m (le_of_lt hm)
    have hmval : ((m : UInt256)).val = m :=
      Nat.mod_eq_of_lt (lt_trans hm (evm.sload 1).isLt)
    have hIXnem : IX ≠ (m : UInt256) := by
      intro h
      apply hmIX
      rw [← hmval, ← h]
    have hmnec : (m : UInt256) ≠ NI := by
      rw [hNI]
      apply Fin.ne_of_val_ne
      rw [hmval]
      omega
    have hvm0 : leafSlot evm (m : UInt256) = wm := (leafSlot_keccak hm0).2
    have hvm4 : leafSlot E4 (m : UInt256) = wm := (leafSlot_keccak hm4).2
    have hkm4 := (leafSlot_keccak hm4).1
    -- keccak-injective separations of the S1 copy slots from wm/wm+2
    have hsep : ∀ a b : UInt256, a.val < Clear.KeccakInjective.lowSlotBound →
        b.val < Clear.KeccakInjective.lowSlotBound → w + a ≠ wm + b := by
      intro a b ha hb
      exact keccak_off_ne_off hkw4 hkm4 (accInterval_ne hIXnem) ha hb
    -- SF → S3
    have htail0 : SF.sload wm = S3.sload wm := by
      have h := htail (m : UInt256) wm 0 hm4 (by decide)
      rw [hvm4] at h
      simpa using h
    have htail2 : SF.sload (wm + 2) = S3.sload (wm + 2) := by
      have h := htail (m : UInt256) wm 2 hm4 (by decide)
      rw [hvm4] at h
      exact h
    -- S3 → S2
    obtain ⟨hmid0, hmid2⟩ := hmid (m : UInt256) wm hmF hmnec
    -- S2 → S1
    have hwalk0 : S2.sload wm = S1.sload wm := by
      have h := updateWalk_sload_leaf kk₁ (k := 0) hm4 (by decide) hok₁
      rw [hvm4] at h
      rw [hS2d]
      simpa using h
    have hwalk2 : S2.sload (wm + 2) = S1.sload (wm + 2) := by
      have h := updateWalk_sload_leaf kk₁ (k := 2) hm4 (by decide) hok₁
      rw [hvm4] at h
      rw [hS2d]
      exact h
    -- S1 → evm
    have hcopy0 : S1.sload wm = evm.sload wm := by
      rw [hS1d, hEKd, hSLd]
      refine (copyChain_sload_ne hclean4 ?_ ?_ ?_).trans (hE4s wm)
      · rw [haccw]
        have h := hsep 0 0 (by decide) (by decide)
        simpa using h
      · rw [haccw]
        have h := hsep 1 0 (by decide) (by decide)
        simpa using h
      · rw [haccw]
        have h := hsep 2 0 (by decide) (by decide)
        simpa using h
    have hcopy2 : S1.sload (wm + 2) = evm.sload (wm + 2) := by
      rw [hS1d, hEKd, hSLd]
      refine (copyChain_sload_ne hclean4 ?_ ?_ ?_).trans (hE4s (wm + 2))
      · rw [haccw]
        have h := hsep 0 2 (by decide) (by decide)
        simpa using h
      · rw [haccw]
        exact hsep 1 2 (by decide) (by decide)
      · rw [haccw]
        exact hsep 2 2 (by decide) (by decide)
    -- assemble the m-chain
    have hSFm : leafSlot SF (m : UInt256) = wm := hslotSF _ _ hmF
    unfold decodeLeaf
    rw [hSFm, hvm0, htail0, hmid0, hwalk0, hcopy0, htail2, hmid2, hwalk2, hcopy2]
  -- ===== per-index: the window leaf =====
  have hIXneNI : IX ≠ NI := by
    rw [hNI]
    exact Fin.ne_of_val_ne (Nat.ne_of_lt hwlt)
  have hwidx : decodeLeaf SF IX = ⟨(decodeLeaf evm IX).key, V⟩ := by
    have htail0 : SF.sload w = S3.sload w := by
      have h := htail IX w 0 hw4 (by decide)
      rw [hvw4] at h
      simpa using h
    have htail2 : SF.sload (w + 2) = S3.sload (w + 2) := by
      have h := htail IX w 2 hw4 (by decide)
      rw [hvw4] at h
      exact h
    obtain ⟨hmid0, hmid2⟩ := hmid IX w hwF hIXneNI
    have hwalk0 : S2.sload w = S1.sload w := by
      have h := updateWalk_sload_leaf kk₁ (k := 0) hw4 (by decide) hok₁
      rw [hvw4] at h
      rw [hS2d]
      simpa using h
    have hwalk2 : S2.sload (w + 2) = S1.sload (w + 2) := by
      have h := updateWalk_sload_leaf kk₁ (k := 2) hw4 (by decide) hok₁
      rw [hvw4] at h
      rw [hS2d]
      exact h
    have hSFw : leafSlot SF IX = w := hslotSF _ _ hwF
    have hstep : decodeLeaf SF IX = ⟨SF.sload w, SF.sload (w + 2)⟩ := by
      unfold decodeLeaf
      rw [hSFw]
    rw [hstep, htail0, hmid0, hwalk0, hS1fields.1, htail2, hmid2, hwalk2,
        hS1fields.2, hkey]
  -- ===== per-index: the new leaf at the count =====
  have hnew : decodeLeaf SF (evm.sload 1) = ⟨V, (decodeLeaf evm IX).nextKey⟩ := by
    have htail0 : SF.sload wc = S3.sload wc := by
      have h := htail (evm.sload 1) wc 0 hc4 (by decide)
      rw [hvc4] at h
      simpa using h
    have htail2 : SF.sload (wc + 2) = S3.sload (wc + 2) := by
      have h := htail (evm.sload 1) wc 2 hc4 (by decide)
      rw [hvc4] at h
      exact h
    have hSFc : leafSlot SF (evm.sload 1) = wc := hslotSF _ _ hcF
    have hstep : decodeLeaf SF (evm.sload 1) = ⟨SF.sload wc, SF.sload (wc + 2)⟩ := by
      unfold decodeLeaf
      rw [hSFc]
    rw [hstep, htail0, hS3fields.1, htail2, hS3fields.2, hnv]
  -- ===== assemble the set equation =====
  unfold leafSetOf
  rw [hcval, Finset.range_succ, Finset.image_insert, hccast, hnew]
  have himg : (Finset.range (evm.sload 1).val).image
        (fun n : ℕ => decodeLeaf SF (n : UInt256))
      = insert (⟨(decodeLeaf evm IX).key, V⟩ : AbsLeaf)
          (((Finset.range (evm.sload 1).val).image
              (fun n : ℕ => decodeLeaf evm (n : UInt256))).erase
            (decodeLeaf evm ((IX.val : ℕ) : UInt256))) := by
    refine image_update_erase_insert hwlt houtside ?_ hinj
    show decodeLeaf SF ((IX.val : ℕ) : UInt256)
      = (⟨(decodeLeaf evm IX).key, V⟩ : AbsLeaf)
    rw [hIXcast]
    exact hwidx
  rw [himg, hIXcast]
  unfold imtInsert
  exact Finset.Insert.comm _ _ _

/-! ### THE INTERLEAVE-ACCURATE VARIANT (the weld target)

`glueSeq_leafSetOf` models the two Merkle segments as BARE walks.  The real
insert glue (`insertGlue_prefix`, `imt_insert_gate_user`) interleaves two
extra step classes that the closed form carries and the bare chain lacks:

  * between the retarget copy `S1` and walk #1, the `updateLeaf_5205` arm
    first HASHES the staged struct (`hashLeafOut` — a keccak step plus five
    scratch/allocator `mstore`s) giving `H1`, then writes the hash into the
    LEVEL-0 node array (`leafWriteEvm H1 ss₀ idx₀ hl₀`) giving `L0`; the
    walk starts at `L0`, not `S1`;
  * between the vti registration `S3` and the count bump, the
    `pushNewLeaf` arm first hashes the new-leaf struct (`pushEH` =
    `hashLeafOut` again) giving `H3`; the bump `sstore`s on `H3`, not `S3`.

`glueSeq_leafSetOf'` absorbs both:

  * `H1`/`H3` enter as GENERIC states with one hypothesis each — storage
    transparency (`∀ t, H·.sload t = S·.sload t`); the weld discharges it
    for the concrete `hashLeafOut` states by `sload_keccakOut_of_clean`
    (hash steps never `sstore`).  Nothing else about the hash steps is
    needed: the `F4` cache facts are pack hypotheses, and walk-1 slot
    frames are pinned at the FIXED reference anchor `E4`
    (`updateWalk_sload_leaf` needs no per-state cache transport);
  * the extra level-0 write `L0` is separated from every leaf-field slot
    by the 32-vs-64 preimage-length split (`keccak_off_ne_off` via
    `leafWrite_sload_ne`), exactly like the `SW` write of the push — at the
    cost of two `arrOut` cleanliness flags and `idx₀ < lowSlotBound`;
  * `H3` REWRITES THE JUNK WINDOW (the `hashLeafOut` allocator bump), so
    the final-state slot pinning can no longer anchor at `F4`: the cache
    pack gains a FOURTH anchor at `H3` (`accInterval H3`), and the
    `SF`-side junk/cache/interval chain (`hjSF`/`hIntSF`/`hmonoSF`/
    `hslotSF`) starts at `H3` instead of `F4`.

Everything else is verbatim `glueSeq_leafSetOf`. -/

open Clear.KeccakDeterminism in
/-- **THE GLUE-SEQUENCE FIDELITY THEOREM, interleave-accurate form** — the
state chain of the REAL insert closed form (`insertGlue_prefix`): retarget
stage + copy → `hashLeaf` #1 (`H1`) → level-0 write → walk #1 → new-leaf
stage + copy + vti → `hashLeaf` #2 (`H3`) → count bump → padding walk →
level-0 write → walk #2 — satisfies

`leafSetOf SF = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V`.

The interleaved hash states `H1`/`H3` are generic, constrained only by
storage transparency; the cache pack is QUAD-anchored (`evm`/`E4`/`F4`/`H3`
— the `hashLeaf` allocator bumps split the chain into four junk-window
regimes).  See the section comment above and `glueSeq_leafSetOf`'s anchor
diagram. -/
theorem glueSeq_leafSetOf'
    {evm H1 H3 : EVMState} {LM NI V IX NI4 NV5 : UInt256}
    {ss₀ idx₀ hl₀ : UInt256}
    {ss₁ base₁ i₁ idx₁ maxN₁ cur₁ : UInt256} {kk₁ : ℕ}
    {ip om mp : UInt256} {kp : ℕ}
    {ssw nidx hl : UInt256}
    {ss₂ base₂ i₂ idx₂ maxN₂ cur₂ : UInt256} {kk₂ : ℕ} :
    let P1 := evm.mload 64
    let E4 := (((evm.mstore 64 (P1 + 96)).mstore P1 (evm.mload LM)).mstore
        (P1 + 32) NI).mstore (P1 + 64) V
    let EK := (accOut E4 IX 4).2
    let SL := (accOut E4 IX 4).1
    let S1 := ((EK.sstore SL (EK.mload P1)).sstore
        (SL + 1) (EK.mload (P1 + 32))).sstore (SL + 2) (EK.mload (P1 + 64))
    let L0 := leafWriteEvm H1 ss₀ idx₀ hl₀
    let S2 := (updateWalk ss₁ base₁ kk₁ L0 i₁ idx₁ maxN₁ cur₁).1
    let P2 := S2.mload 64
    let F4 := (((S2.mstore 64 (P2 + 96)).mstore P2 V).mstore
        (P2 + 32) NI4).mstore (P2 + 64) NV5
    let FK := (accOut F4 NI 4).2
    let SL2 := (accOut F4 NI 4).1
    let F5 := ((FK.sstore SL2 (FK.mload P2)).sstore
        (SL2 + 1) (FK.mload (P2 + 32))).sstore (SL2 + 2) (FK.mload (P2 + 64))
    let S3 := (accOut F5 V 5).2.sstore ((accOut F5 V 5).1) NI
    let SB := H3.sstore 1 (H3.sload 1 + 1)
    let SP := (padWalk kp SB ip om mp).1
    let SW := leafWriteEvm SP ssw nidx hl
    let SF := (updateWalk ss₂ base₂ kk₂ SW i₂ idx₂ maxN₂ cur₂).1
    -- window guard and count arithmetic
    IX.val < (evm.sload 1).val →
    (evm.sload 1).val + 1 < 2 ^ 256 →
    NI = evm.sload 1 →
    -- guard-phase read-backs binding the staged values to σ₀-decodes
    evm.mload LM = (decodeLeaf evm IX).key →
    NV5 = (decodeLeaf evm IX).nextKey →
    -- the interleaved hash steps are storage-transparent
    (∀ t : UInt256, H1.sload t = S1.sload t) →
    (∀ t : UInt256, H3.sload t = S3.sload t) →
    -- allocator bounds per staging segment
    96 ≤ P1.val → P1.val + 128 ≤ 2 ^ 256 →
    96 ≤ P2.val → P2.val + 128 ≤ 2 ^ 256 →
    -- cleanliness per accessor / arrOut scratch
    (accOut E4 IX 4).2.hash_collision = false →
    (accOut F4 NI 4).2.hash_collision = false →
    (accOut F5 V 5).2.hash_collision = false →
    (arrOut H1 (ss₀ + 2)).2.hash_collision = false →
    (arrOut (arrOut H1 (ss₀ + 2)).2 (arrOut H1 (ss₀ + 2)).1).2.hash_collision
      = false →
    (arrOut SP (ssw + 2)).2.hash_collision = false →
    (arrOut (arrOut SP (ssw + 2)).2 (arrOut SP (ssw + 2)).1).2.hash_collision
      = false →
    -- account presence where `sload_sstore_self` fires
    (EK.lookupAccount EK.execution_env.code_owner).isSome →
    (FK.lookupAccount FK.execution_env.code_owner).isSome →
    (H3.lookupAccount H3.execution_env.code_owner).isSome →
    -- the level-0 element indices are small
    idx₀.val < Clear.KeccakInjective.lowSlotBound →
    nidx.val < Clear.KeccakInjective.lowSlotBound →
    -- the quad-anchor cache pack (see the section comment)
    (∀ m : ℕ, m ≤ (evm.sload 1).val → ∃ wm,
      Finmap.lookup (accInterval evm (m : UInt256) 4) evm.keccak_map = some wm
      ∧ Finmap.lookup (accInterval E4 (m : UInt256) 4) E4.keccak_map = some wm
      ∧ Finmap.lookup (accInterval F4 (m : UInt256) 4) F4.keccak_map = some wm
      ∧ Finmap.lookup (accInterval H3 (m : UInt256) 4) H3.keccak_map = some wm) →
    -- decode injectivity below the count at σ₀
    (∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m') →
    -- the walks' low-slot packs
    (∀ j, j < kk₁ →
      StepLowOK ss₁ base₁ (updateWalk ss₁ base₁ j L0 i₁ idx₁ maxN₁ cur₁)) →
    (∀ j, j < kp → PadLowOK (padWalk j SB ip om mp)) →
    (∀ j, j < kk₂ →
      StepLowOK ss₂ base₂ (updateWalk ss₂ base₂ j SW i₂ idx₂ maxN₂ cur₂)) →
    leafSetOf SF = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
  intro P1 E4 EK SL S1 L0 S2 P2 F4 FK SL2 F5 S3 SB SP SW SF
  intro hwlt hnw hNI hkey hnv hH1s hH3s hplow1 hnw1 hplow2 hnw2
  intro hclean4 hcleanF hcleanV hcleanB1 hcleanB2 hcleanA1 hcleanA2
  intro haccEK haccFK haccH3 hidx₀ hnidx
  intro hcach hinj hok₁ hokp hok₂
  -- definitional handles on the chain
  have hEKd : EK = (accOut E4 IX 4).2 := rfl
  have hSLd : SL = (accOut E4 IX 4).1 := rfl
  have hS1d : S1 = ((EK.sstore SL (EK.mload P1)).sstore
      (SL + 1) (EK.mload (P1 + 32))).sstore (SL + 2) (EK.mload (P1 + 64)) := rfl
  have hL0d : L0 = leafWriteEvm H1 ss₀ idx₀ hl₀ := rfl
  have hS2d : S2 = (updateWalk ss₁ base₁ kk₁ L0 i₁ idx₁ maxN₁ cur₁).1 := rfl
  have hFKd : FK = (accOut F4 NI 4).2 := rfl
  have hSL2d : SL2 = (accOut F4 NI 4).1 := rfl
  have hF5d : F5 = ((FK.sstore SL2 (FK.mload P2)).sstore
      (SL2 + 1) (FK.mload (P2 + 32))).sstore (SL2 + 2) (FK.mload (P2 + 64)) := rfl
  have hS3d : S3 = (accOut F5 V 5).2.sstore ((accOut F5 V 5).1) NI := rfl
  have hSBd : SB = H3.sstore 1 (H3.sload 1 + 1) := rfl
  have hSPd : SP = (padWalk kp SB ip om mp).1 := rfl
  have hSWd : SW = leafWriteEvm SP ssw nidx hl := rfl
  have hSFd : SF = (updateWalk ss₂ base₂ kk₂ SW i₂ idx₂ maxN₂ cur₂).1 := rfl
  -- the staging `mstore`s are storage-transparent
  have hE4s : ∀ t : UInt256, E4.sload t = evm.sload t := fun _ => rfl
  have hF4s : ∀ t : UInt256, F4.sload t = S2.sload t := fun _ => rfl
  -- casts
  have hIXcast : ((IX.val : ℕ) : UInt256) = IX := Fin.cast_val_eq_self IX
  have hccast : (((evm.sload 1).val : ℕ) : UInt256) = evm.sload 1 :=
    Fin.cast_val_eq_self (evm.sload 1)
  -- the anchor caches of the window index and the count
  obtain ⟨w, hw0, hw4, hwF, hwH⟩ := hcach IX.val (le_of_lt hwlt)
  rw [hIXcast] at hw0 hw4 hwF hwH
  obtain ⟨wc, hc0, hc4, hcF, hcH⟩ := hcach (evm.sload 1).val (le_refl _)
  rw [hccast] at hc0 hc4 hcF hcH
  clear hw0 hc0
  -- slot pinning at the anchors
  have hvw4 : leafSlot E4 IX = w := (leafSlot_keccak hw4).2
  have hkw4 := (leafSlot_keccak hw4).1
  have hvc4 : leafSlot E4 (evm.sload 1) = wc := (leafSlot_keccak hc4).2
  have hkcF := (leafSlot_keccak hcF).1
  have haccw : (accOut E4 IX 4).1 = w := hvw4
  have haccwc : (accOut F4 NI 4).1 = wc := by
    rw [hNI]
    exact (leafSlot_keccak hcF).2
  -- collision-flag backchain to the F4 anchor
  have hcolF4 : F4.hash_collision = false := accOut_clean_backward hcleanF
  -- ===== the count chain: SF.sload 1 = count + 1 =====
  have hcntS1 : S1.sload 1 = evm.sload 1 := by
    rw [hS1d, hEKd, hSLd]
    refine (copyChain_sload_ne hclean4 ?_ ?_ ?_).trans (hE4s 1)
    · rw [haccw]
      exact Clear.KeccakInjective.keccak256_ne_lowSlot 1 hkw4 (by decide)
    · rw [haccw]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 1 1 hkw4
        (by decide) (by decide)
    · rw [haccw]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 2 1 hkw4
        (by decide) (by decide)
  have hcntS2 : S2.sload 1 = evm.sload 1 := by
    rw [hS2d, updateWalk_sload_one kk₁ hok₁, hL0d]
    have hne : (arrOut (arrOut H1 (ss₀ + 2)).2 (arrOut H1 (ss₀ + 2)).1).1 + idx₀
        ≠ (1 : UInt256) :=
      Clear.KeccakInjective.keccak256_add_ne_lowSlot idx₀ 1 (arrOut_pair hcleanB2)
        hidx₀ (by decide)
    rw [leafWrite_sload_ne hcleanB1 hcleanB2 hne, hH1s 1]
    exact hcntS1
  have hcntF5 : F5.sload 1 = evm.sload 1 := by
    rw [hF5d, hFKd, hSL2d]
    refine (copyChain_sload_ne hcleanF ?_ ?_ ?_).trans ((hF4s 1).trans hcntS2)
    · rw [haccwc]
      exact Clear.KeccakInjective.keccak256_ne_lowSlot 1 hkcF (by decide)
    · rw [haccwc]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 1 1 hkcF
        (by decide) (by decide)
    · rw [haccwc]
      exact Clear.KeccakInjective.keccak256_add_ne_lowSlot 2 1 hkcF
        (by decide) (by decide)
  -- the vti write slot, pinned to the accessor's own output
  have hcvF' : Finmap.lookup (accInterval (accOut F5 V 5).2 V 5)
      ((accOut F5 V 5).2).keccak_map = some ((accOut F5 V 5).1) := by
    rw [show accInterval (accOut F5 V 5).2 V 5 = accInterval F5 V 5 from
      accInterval_eq (fun _ hx1 _ => accOut_junk_window hx1)]
    exact accOut_caches_of_clean hcleanV
  have hvtiSlot : vtiSlot (accOut F5 V 5).2 V = (accOut F5 V 5).1 :=
    accOut_agree_value (fun _ hx1 _ => (accOut_junk_window hx1).symm)
      (accOut_caches_of_clean hcleanV)
  have hcntS3 : S3.sload 1 = evm.sload 1 := by
    rw [hS3d]
    have h := leafCount_vtiWrite (σ := (accOut F5 V 5).2) (v := V) (u := NI) hcvF'
    rw [hvtiSlot] at h
    rw [h, sload_accOut_of_clean 1 hcleanV]
    exact hcntF5
  have hcntSB : SB.sload 1 = evm.sload 1 + 1 := by
    rw [hSBd, sload_sstore_self haccH3, hH3s 1, hcntS3]
  have hcntSP : SP.sload 1 = evm.sload 1 + 1 := by
    rw [hSPd, padWalk_sload_one kp hokp]
    exact hcntSB
  have hcntSW : SW.sload 1 = evm.sload 1 + 1 := by
    rw [hSWd]
    have hne : (arrOut (arrOut SP (ssw + 2)).2 (arrOut SP (ssw + 2)).1).1 + nidx
        ≠ (1 : UInt256) :=
      Clear.KeccakInjective.keccak256_add_ne_lowSlot nidx 1 (arrOut_pair hcleanA2)
        hnidx (by decide)
    rw [leafWrite_sload_ne hcleanA1 hcleanA2 hne]
    exact hcntSP
  have hcntSF : SF.sload 1 = evm.sload 1 + 1 := by
    rw [hSFd, updateWalk_sload_one kk₂ hok₂]
    exact hcntSW
  have hcval : (SF.sload 1).val = (evm.sload 1).val + 1 := by
    rw [hcntSF]
    show ((evm.sload 1).val + (1 : UInt256).val) % 2 ^ 256 = (evm.sload 1).val + 1
    have h1v : ((1 : UInt256)).val = 1 := rfl
    rw [h1v]
    exact Nat.mod_eq_of_lt hnw
  -- ===== junk-window frames (E4 → S1, F4 → S3, H3 → SF) =====
  have hjS1 : ∀ b : UInt256, 64 ≤ b.val →
      Finmap.lookup b S1.machine_state.memory
        = Finmap.lookup b E4.machine_state.memory := by
    intro b hb
    rw [hS1d, machine_state_sstore', machine_state_sstore', machine_state_sstore',
        hEKd, accOut_junk_window hb]
  have hjS3 : ∀ b : UInt256, 64 ≤ b.val →
      Finmap.lookup b S3.machine_state.memory
        = Finmap.lookup b F4.machine_state.memory := by
    intro b hb
    rw [hS3d, machine_state_sstore', accOut_junk_window hb, hF5d,
        machine_state_sstore', machine_state_sstore', machine_state_sstore',
        hFKd, accOut_junk_window hb]
  have hjSF : ∀ b : UInt256, 64 ≤ b.val →
      Finmap.lookup b SF.machine_state.memory
        = Finmap.lookup b H3.machine_state.memory := by
    intro b hb
    rw [hSFd, updateWalk_junk kk₂ hb, hSWd]
    unfold leafWriteEvm
    rw [machine_state_sstore', arrOut_junk_f hb, arrOut_junk_f hb,
        hSPd, padWalk_junk kp hb, hSBd, machine_state_sstore']
  have hIntS1 : ∀ i : UInt256, accInterval S1 i 4 = accInterval E4 i 4 :=
    fun _ => accInterval_eq (fun b hb1 _ => hjS1 b hb1)
  have hIntS3 : ∀ i : UInt256, accInterval S3 i 4 = accInterval F4 i 4 :=
    fun _ => accInterval_eq (fun b hb1 _ => hjS3 b hb1)
  have hIntSF : ∀ i : UInt256, accInterval SF i 4 = accInterval H3 i 4 :=
    fun _ => accInterval_eq (fun b hb1 _ => hjSF b hb1)
  -- ===== cache-monotonicity chains =====
  have hmonoS1 : ∀ (I : List UInt256) (u : UInt256),
      Finmap.lookup I E4.keccak_map = some u →
      Finmap.lookup I S1.keccak_map = some u := by
    intro I u hI
    rw [hS1d, keccak_map_sstore', keccak_map_sstore', keccak_map_sstore', hEKd]
    exact cached_after_accOut hI
  have hmonoS3 : ∀ (I : List UInt256) (u : UInt256),
      Finmap.lookup I F4.keccak_map = some u →
      Finmap.lookup I S3.keccak_map = some u := by
    intro I u hI
    rw [hS3d, keccak_map_sstore']
    refine cached_after_accOut ?_
    rw [hF5d, keccak_map_sstore', keccak_map_sstore', keccak_map_sstore', hFKd]
    exact cached_after_accOut hI
  have hmonoSF : ∀ (I : List UInt256) (u : UInt256),
      Finmap.lookup I H3.keccak_map = some u →
      Finmap.lookup I SF.keccak_map = some u := by
    intro I u hI
    rw [hSFd]
    refine updateWalk_lookup_mono kk₂ ?_
    rw [hSWd]
    unfold leafWriteEvm
    rw [keccak_map_sstore']
    refine arrOut_mono_f (arrOut_mono_f ?_)
    rw [hSPd]
    refine padWalk_lookup_mono kp ?_
    rw [hSBd, keccak_map_sstore']
    exact hI
  -- final-state slot pinning (H3-anchored caches survive to SF)
  have hslotSF : ∀ n u : UInt256,
      Finmap.lookup (accInterval H3 n 4) H3.keccak_map = some u →
      leafSlot SF n = u := by
    intro n u hn
    have h : Finmap.lookup (accInterval SF n 4) SF.keccak_map = some u := by
      rw [hIntSF n]
      exact hmonoSF _ _ hn
    exact (leafSlot_keccak h).2
  -- ===== the S1 copy values (retargetStage_decode, slot re-pinned) =====
  have hdecS1 : decodeLeaf S1 IX = ⟨evm.mload LM, V⟩ :=
    retargetStage_decode (evm := evm) (LM := LM) (NI := NI) (V := V) (IX := IX)
      hclean4 haccEK hplow1 hnw1
  have hslotS1IX : leafSlot S1 IX = w := by
    have h : Finmap.lookup (accInterval S1 IX 4) S1.keccak_map = some w := by
      rw [hIntS1 IX]
      exact hmonoS1 _ _ hw4
    exact (leafSlot_keccak h).2
  have hS1fields : S1.sload w = evm.mload LM ∧ S1.sload (w + 2) = V := by
    have h := hdecS1
    unfold decodeLeaf at h
    rw [hslotS1IX] at h
    exact ⟨congrArg AbsLeaf.key h, congrArg AbsLeaf.nextKey h⟩
  -- ===== the S3 copy values (newLeafStage_decode, slot re-pinned) =====
  have hdecS3 : decodeLeaf S3 NI = ⟨V, NV5⟩ :=
    newLeafStage_decode (evm := S2) (V := V) (NI4 := NI4) (NV5 := NV5) (IX1 := NI)
      hcleanF hcleanV haccFK hplow2 hnw2
  have hslotS3NI : leafSlot S3 NI = wc := by
    have h : Finmap.lookup (accInterval S3 NI 4) S3.keccak_map = some wc := by
      rw [hIntS3 NI, hNI]
      exact hmonoS3 _ _ hcF
    exact (leafSlot_keccak h).2
  have hS3fields : S3.sload wc = V ∧ S3.sload (wc + 2) = NV5 := by
    have h := hdecS3
    unfold decodeLeaf at h
    rw [hslotS3NI] at h
    exact ⟨congrArg AbsLeaf.key h, congrArg AbsLeaf.nextKey h⟩
  -- ===== the S3 → SF tail frame at any E4-anchored leaf slot =====
  have htail : ∀ n u k : UInt256,
      Finmap.lookup (accInterval E4 n 4) E4.keccak_map = some u →
      k.val < Clear.KeccakInjective.lowSlotBound →
      SF.sload (leafSlot E4 n + k) = S3.sload (leafSlot E4 n + k) := by
    intro n u k hcE hk
    rw [hSFd, updateWalk_sload_leaf kk₂ hcE hk hok₂, hSWd]
    have hne : (arrOut (arrOut SP (ssw + 2)).2 (arrOut SP (ssw + 2)).1).1 + nidx
        ≠ leafSlot E4 n + k := by
      obtain ⟨hki, hvi⟩ := leafSlot_keccak hcE
      rw [hvi]
      exact keccak_off_ne_off (arrOut_pair hcleanA2) hki
        (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hnidx hk
    rw [leafWrite_sload_ne hcleanA1 hcleanA2 hne,
        hSPd, padWalk_sload_leaf kp hcE hk hokp,
        hSBd, sload_sstore_ne (Ne.symm (leafSlot_add_ne_low k 1 hcE hk (by decide)))]
    exact hH3s _
  -- ===== the S1 → S2 walk-1 frame at any E4-anchored leaf slot =====
  have htail1 : ∀ n u k : UInt256,
      Finmap.lookup (accInterval E4 n 4) E4.keccak_map = some u →
      k.val < Clear.KeccakInjective.lowSlotBound →
      S2.sload (leafSlot E4 n + k) = S1.sload (leafSlot E4 n + k) := by
    intro n u k hcE hk
    rw [hS2d, updateWalk_sload_leaf kk₁ hcE hk hok₁, hL0d]
    have hne : (arrOut (arrOut H1 (ss₀ + 2)).2 (arrOut H1 (ss₀ + 2)).1).1 + idx₀
        ≠ leafSlot E4 n + k := by
      obtain ⟨hki, hvi⟩ := leafSlot_keccak hcE
      rw [hvi]
      exact keccak_off_ne_off (arrOut_pair hcleanB2) hki
        (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hidx₀ hk
    rw [leafWrite_sload_ne hcleanB1 hcleanB2 hne]
    exact hH1s _
  -- ===== the S2 → S3 middle frame for non-count indices =====
  have hmid : ∀ n u : UInt256,
      Finmap.lookup (accInterval F4 n 4) F4.keccak_map = some u →
      n ≠ NI →
      S3.sload u = S2.sload u ∧ S3.sload (u + 2) = S2.sload (u + 2) := by
    intro n u hcFn hne
    have hcleann : (accOut F4 n 4).2.hash_collision = false := by
      rw [accOut_of_cached hcFn]
      show ((F4.mstore 0 n).mstore 32 4).hash_collision = false
      rw [hash_collision_mstore, hash_collision_mstore]
      exact hcolF4
    have hdec : decodeLeaf S3 n = decodeLeaf F4 n :=
      decodeLeaf_stage_outside (evm := S2) (V := V) (NI4 := NI4) (NV5 := NV5)
        (IX1 := NI) (m := n) (wm := u) hcleanF hcleanV hcFn hcleann hne
    have hsS3 : leafSlot S3 n = u := by
      have h : Finmap.lookup (accInterval S3 n 4) S3.keccak_map = some u := by
        rw [hIntS3 n]
        exact hmonoS3 _ _ hcFn
      exact (leafSlot_keccak h).2
    have hsF4 : leafSlot F4 n = u := (leafSlot_keccak hcFn).2
    unfold decodeLeaf at hdec
    rw [hsS3, hsF4] at hdec
    exact ⟨(congrArg AbsLeaf.key hdec).trans (hF4s u),
           (congrArg AbsLeaf.nextKey hdec).trans (hF4s (u + 2))⟩
  -- ===== per-index: below-count, non-window =====
  have houtside : ∀ m : ℕ, m < (evm.sload 1).val → m ≠ IX.val →
      decodeLeaf SF (m : UInt256) = decodeLeaf evm (m : UInt256) := by
    intro m hm hmIX
    obtain ⟨wm, hm0, hm4, hmF, hmH⟩ := hcach m (le_of_lt hm)
    have hmval : ((m : UInt256)).val = m :=
      Nat.mod_eq_of_lt (lt_trans hm (evm.sload 1).isLt)
    have hIXnem : IX ≠ (m : UInt256) := by
      intro h
      apply hmIX
      rw [← hmval, ← h]
    have hmnec : (m : UInt256) ≠ NI := by
      rw [hNI]
      apply Fin.ne_of_val_ne
      rw [hmval]
      omega
    have hvm0 : leafSlot evm (m : UInt256) = wm := (leafSlot_keccak hm0).2
    have hvm4 : leafSlot E4 (m : UInt256) = wm := (leafSlot_keccak hm4).2
    have hkm4 := (leafSlot_keccak hm4).1
    -- keccak-injective separations of the S1 copy slots from wm/wm+2
    have hsep : ∀ a b : UInt256, a.val < Clear.KeccakInjective.lowSlotBound →
        b.val < Clear.KeccakInjective.lowSlotBound → w + a ≠ wm + b := by
      intro a b ha hb
      exact keccak_off_ne_off hkw4 hkm4 (accInterval_ne hIXnem) ha hb
    -- SF → S3
    have htail0 : SF.sload wm = S3.sload wm := by
      have h := htail (m : UInt256) wm 0 hm4 (by decide)
      rw [hvm4] at h
      simpa using h
    have htail2 : SF.sload (wm + 2) = S3.sload (wm + 2) := by
      have h := htail (m : UInt256) wm 2 hm4 (by decide)
      rw [hvm4] at h
      exact h
    -- S3 → S2
    obtain ⟨hmid0, hmid2⟩ := hmid (m : UInt256) wm hmF hmnec
    -- S2 → S1 (through the interleaved hash + level-0 write)
    have hwalk0 : S2.sload wm = S1.sload wm := by
      have h := htail1 (m : UInt256) wm 0 hm4 (by decide)
      rw [hvm4] at h
      simpa using h
    have hwalk2 : S2.sload (wm + 2) = S1.sload (wm + 2) := by
      have h := htail1 (m : UInt256) wm 2 hm4 (by decide)
      rw [hvm4] at h
      exact h
    -- S1 → evm
    have hcopy0 : S1.sload wm = evm.sload wm := by
      rw [hS1d, hEKd, hSLd]
      refine (copyChain_sload_ne hclean4 ?_ ?_ ?_).trans (hE4s wm)
      · rw [haccw]
        have h := hsep 0 0 (by decide) (by decide)
        simpa using h
      · rw [haccw]
        have h := hsep 1 0 (by decide) (by decide)
        simpa using h
      · rw [haccw]
        have h := hsep 2 0 (by decide) (by decide)
        simpa using h
    have hcopy2 : S1.sload (wm + 2) = evm.sload (wm + 2) := by
      rw [hS1d, hEKd, hSLd]
      refine (copyChain_sload_ne hclean4 ?_ ?_ ?_).trans (hE4s (wm + 2))
      · rw [haccw]
        have h := hsep 0 2 (by decide) (by decide)
        simpa using h
      · rw [haccw]
        exact hsep 1 2 (by decide) (by decide)
      · rw [haccw]
        exact hsep 2 2 (by decide) (by decide)
    -- assemble the m-chain
    have hSFm : leafSlot SF (m : UInt256) = wm := hslotSF _ _ hmH
    unfold decodeLeaf
    rw [hSFm, hvm0, htail0, hmid0, hwalk0, hcopy0, htail2, hmid2, hwalk2, hcopy2]
  -- ===== per-index: the window leaf =====
  have hIXneNI : IX ≠ NI := by
    rw [hNI]
    exact Fin.ne_of_val_ne (Nat.ne_of_lt hwlt)
  have hwidx : decodeLeaf SF IX = ⟨(decodeLeaf evm IX).key, V⟩ := by
    have htail0 : SF.sload w = S3.sload w := by
      have h := htail IX w 0 hw4 (by decide)
      rw [hvw4] at h
      simpa using h
    have htail2 : SF.sload (w + 2) = S3.sload (w + 2) := by
      have h := htail IX w 2 hw4 (by decide)
      rw [hvw4] at h
      exact h
    obtain ⟨hmid0, hmid2⟩ := hmid IX w hwF hIXneNI
    have hwalk0 : S2.sload w = S1.sload w := by
      have h := htail1 IX w 0 hw4 (by decide)
      rw [hvw4] at h
      simpa using h
    have hwalk2 : S2.sload (w + 2) = S1.sload (w + 2) := by
      have h := htail1 IX w 2 hw4 (by decide)
      rw [hvw4] at h
      exact h
    have hSFw : leafSlot SF IX = w := hslotSF _ _ hwH
    have hstep : decodeLeaf SF IX = ⟨SF.sload w, SF.sload (w + 2)⟩ := by
      unfold decodeLeaf
      rw [hSFw]
    rw [hstep, htail0, hmid0, hwalk0, hS1fields.1, htail2, hmid2, hwalk2,
        hS1fields.2, hkey]
  -- ===== per-index: the new leaf at the count =====
  have hnew : decodeLeaf SF (evm.sload 1) = ⟨V, (decodeLeaf evm IX).nextKey⟩ := by
    have htail0 : SF.sload wc = S3.sload wc := by
      have h := htail (evm.sload 1) wc 0 hc4 (by decide)
      rw [hvc4] at h
      simpa using h
    have htail2 : SF.sload (wc + 2) = S3.sload (wc + 2) := by
      have h := htail (evm.sload 1) wc 2 hc4 (by decide)
      rw [hvc4] at h
      exact h
    have hSFc : leafSlot SF (evm.sload 1) = wc := hslotSF _ _ hcH
    have hstep : decodeLeaf SF (evm.sload 1) = ⟨SF.sload wc, SF.sload (wc + 2)⟩ := by
      unfold decodeLeaf
      rw [hSFc]
    rw [hstep, htail0, hS3fields.1, htail2, hS3fields.2, hnv]
  -- ===== assemble the set equation =====
  unfold leafSetOf
  rw [hcval, Finset.range_succ, Finset.image_insert, hccast, hnew]
  have himg : (Finset.range (evm.sload 1).val).image
        (fun n : ℕ => decodeLeaf SF (n : UInt256))
      = insert (⟨(decodeLeaf evm IX).key, V⟩ : AbsLeaf)
          (((Finset.range (evm.sload 1).val).image
              (fun n : ℕ => decodeLeaf evm (n : UInt256))).erase
            (decodeLeaf evm ((IX.val : ℕ) : UInt256))) := by
    refine image_update_erase_insert hwlt houtside ?_ hinj
    show decodeLeaf SF ((IX.val : ℕ) : UInt256)
      = (⟨(decodeLeaf evm IX).key, V⟩ : AbsLeaf)
    rw [hIXcast]
    exact hwidx
  rw [himg, hIXcast]
  unfold imtInsert
  exact Finset.Insert.comm _ _ _

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
