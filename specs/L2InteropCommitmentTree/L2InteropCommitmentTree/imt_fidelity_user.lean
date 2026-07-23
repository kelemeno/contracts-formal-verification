import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.IMTAbstract
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
