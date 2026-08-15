import Clear.ReasoningPrinciple

import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_weld_user

/-
  VTI-COHERENCE (#69): the `valueToIndex` storage invariant that closes the
  `hfresh` residue of the Evolution packaging (#68).

  #68 (`insertGlue_evolution_step`, imt_weld_user) proved that the insert
  dispatcher's pass state IS the abstract `Evolution` insert step — up to ONE
  genuinely new obligation, `hfresh : V ∉ keys (leafSetOf evm)`.  Its concrete
  pin exists (the dedup gate: `insertGlue_prefix`'s `hz` says the sload of
  `valueToIndex[V]` is 0), but identifying storage-zero with abstract
  key-freshness needs a storage invariant.  This file builds it:

  * `vtiAt σ v` — the `valueToIndex[v]` storage read (`vtiSlot`, base slot 5);
  * `VtiCoherent σ` — every decoded leaf key EXCEPT 0 has a NONZERO
    `valueToIndex` entry.  The `key ≠ 0` carve-out is forced by the genesis:
    `IndexedMerkleTree.setup` seeds `leaves[0] = ⟨0,0,0⟩` but never writes
    `valueToIndex[0]` (IndexedMerkleTree.sol:42-50), so the genesis leaf's key
    0 has vti entry 0 along every real history;
  * THE BRIDGE (`hfresh_of_vtiCoherent` / `hfresh_of_dedup_gate`):
    coherence + the dedup-gate zero + `V ≠ 0` (the `insert_valueZero` guard)
    give exactly `hfresh`.  `hz` is stated at the guards-threaded state; the
    accessor is storage-transparent when clean, so the entry-state transport
    is definitional — no extra pack word is needed for the bridge;
  * PRESERVATION (`vtiCoherent_preserved`): coherence survives the WHOLE
    dispatcher write chain `wFinal`.  Old keys' vti slots are untouched (the
    single vti write is at `V`'s slot — keccak injectivity separates distinct
    keys' base-5 slots; leaf-struct copies are base-4 — the preimages differ
    at word 32; walk/pad/level-0 writes are 32-byte-preimage array slots —
    the preimage LENGTHS differ; the count bump is a low slot).  `V`'s new
    entry is the old count `NI = evm.sload 1`, nonzero by the glue's own
    initialized guard (`h1nz` — genesis seeds leaf 0, so the count ≥ 1 on any
    real history AND the contract reverts otherwise);
  * THE CLOSED CAPSTONE (`insertGlue_evolution_closed`): #68 restated with
    `hfresh` REPLACED by `VtiCoherent evm` + the gate pins, AND concluding
    `VtiCoherent (wFinal …)` — invariant in, invariant out: the theorem is
    self-sustaining along a history.

  CACHE-PACK DISCIPLINE: as everywhere in the fidelity corpus, keccak slots
  drift with the junk window (bytes [64,95)), so cross-state slot identity is
  carried by cached words.  The vti slots need only TWO anchors per key —
  entry and `H3` (the last allocator bump; everything after `wH3` preserves
  bytes ≥ 64) — plus, for `V`, the write-site anchor `F5` tied to the same
  word (`hvtiV`).  These pack entries are the concrete shadow of "keccak is a
  function of the preimage bytes", which the model's junk-window artifact
  otherwise loses; they are hypotheses in exactly the five-anchor style of
  the weld's leaf pack.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     IMTAbstract Clear.KeccakDeterminism

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.dupNamespace false

/-! ### Local re-derivations of small private helpers

The fidelity file keeps these `private`; they are tiny and re-derived here
verbatim rather than widening that file's surface. -/

/-- `sstore` leaves the machine state (memory) unchanged. -/
private lemma machine_state_sstoreV (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).machine_state = σ.machine_state := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- `sstore` leaves the keccak cache unchanged. -/
private lemma keccak_map_sstoreV (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).keccak_map = σ.keccak_map := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- `sstore` leaves the collision flag unchanged. -/
private lemma hash_collision_sstoreV (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).hash_collision = σ.hash_collision := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- Cached preimage ⇒ `keccakOut` returns the cached word. -/
private lemma keccakOut_fst_cachedV {σ : EVMState} {p n w : UInt256}
    (h : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map = some w) :
    (keccakOut σ p n).1 = w := by
  unfold keccakOut EVMState.keccak256
  simp only [h]

/-- The cached-hash success witness for a `valueToIndex` slot (base 5). -/
private lemma vtiSlot_keccakV {σ : EVMState} {v w : UInt256}
    (hc : Finmap.lookup (accInterval σ v 5) σ.keccak_map = some w) :
    ((σ.mstore 0 v).mstore 32 5).keccak256 0 64
      = some (w, (σ.mstore 0 v).mstore 32 5)
    ∧ vtiSlot σ v = w := by
  have hkm : ((σ.mstore 0 v).mstore 32 5).keccak_map = σ.keccak_map := by
    rw [keccak_map_mstore, keccak_map_mstore]
  constructor
  · exact Clear.KeccakInjective.keccak256_of_cached (by rw [hkm]; exact hc)
  · exact keccakOut_fst_cachedV (by rw [hkm]; exact hc)

/-- Two 64-byte accessor preimages differ when the word at address 0 (the
mapping KEY word) differs. -/
private lemma mkInterval_word0_neV {ms₁ ms₂ : MachineState}
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

/-- The accessor scratch reads the key back at address 0. -/
private lemma accWord0V (σ : EVMState) (key base : UInt256) :
    ((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory (0 : UInt256)
      = key := by
  show ((σ.mstore 0 key).mstore 32 base).mload 0 = key
  rw [mload_mstore_outside _ _ _ _ (by decide) (by decide) (Or.inl (by decide))]
  exact mload_mstore_self_at σ 0 key (by decide)

/-- Distinct keys give distinct base-5 accessor preimages (word 0). -/
private lemma vtiInterval_neV {σ₁ σ₂ : EVMState} {x y : UInt256} (hxy : x ≠ y) :
    mkInterval ((σ₁.mstore 0 x).mstore 32 5).machine_state 0 64
      ≠ mkInterval ((σ₂.mstore 0 y).mstore 32 5).machine_state 0 64 := by
  apply mkInterval_word0_neV
  rw [accWord0V, accWord0V]
  exact hxy

/-- Base-5 and base-4 accessor preimages differ (word 32). -/
private lemma base54_interval_neV {σ₁ σ₂ : EVMState} {x y : UInt256} :
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

/-- The keccak success witness of a clean `arrOut` step, `keccak256` form. -/
private lemma arrOut_pairV {σ : EVMState} {a : UInt256}
    (h : (arrOut σ a).2.hash_collision = false) :
    (σ.mstore 0 a).keccak256 0 32 = some ((arrOut σ a).1, (arrOut σ a).2) := by
  have hksome := keccakOut_some_of_clean
    (σ := σ.mstore 0 a) (p := 0) (n := 32) (by exact h)
  rw [hksome]
  rfl

/-- Collision-flag monotonicity, backwards through `arrOut`. -/
private lemma arrOut_clean_bwV {σ : EVMState} {a : UInt256}
    (h : (arrOut σ a).2.hash_collision = false) : σ.hash_collision = false := by
  have := keccakOut_clean_backward (σ := σ.mstore 0 a) (p := 0) (n := 32)
    (by exact h)
  rwa [hash_collision_mstore] at this

/-- The scratch `mstore`s preserve the junk window. -/
private lemma mstore_junkV {σ : EVMState} {a v : UInt256} {b : UInt256}
    (ha : a.val + 32 ≤ 64) (hb : 64 ≤ b.val) :
    Finmap.lookup b (σ.mstore a v).machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  apply lookup_updateMemory_outside_val
  · omega
  · right
    omega

/-- `arrOut` preserves the junk window (its scratch is `[0, 32)`). -/
private lemma arrOut_junkV {σ : EVMState} {a : UInt256} {b : UInt256}
    (hb : 64 ≤ b.val) :
    Finmap.lookup b (arrOut σ a).2.machine_state.memory
      = Finmap.lookup b σ.machine_state.memory := by
  unfold arrOut
  rw [keccakOut_machine_state]
  exact mstore_junkV (by rw [(by decide : ((0 : UInt256)).val = 0)]; omega) hb

/-- `arrOut` only grows the keccak cache. -/
private lemma arrOut_monoV {σ : EVMState} {a : UInt256}
    {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (arrOut σ a).2.keccak_map = some w := by
  unfold arrOut
  apply keccakOut_lookup_mono
  rwa [keccak_map_mstore]

/-- The three-field struct copy over an accessor thread preserves any slot
separated from its three write slots. -/
private lemma copyChain_sload_neV {σ4 : EVMState} {I x y z t : UInt256}
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
slot. -/
private lemma leafWrite_sload_neV {σ : EVMState} {ss idx leaf t : UInt256}
    (hA1 : (arrOut σ (ss + 2)).2.hash_collision = false)
    (hA2 : (arrOut (arrOut σ (ss + 2)).2 (arrOut σ (ss + 2)).1).2.hash_collision
      = false)
    (hne : (arrOut (arrOut σ (ss + 2)).2 (arrOut σ (ss + 2)).1).1 + idx ≠ t) :
    (leafWriteEvm σ ss idx leaf).sload t = σ.sload t := by
  unfold leafWriteEvm
  rw [sload_sstore_ne hne, sload_arrOut_of_clean t hA2,
      sload_arrOut_of_clean t hA1]

/-! ### THE INVARIANT -/

/-- The `valueToIndex[v]` storage read (mapping base slot 5, `vtiSlot`). -/
def vtiAt (σ : EVMState) (v : UInt256) : UInt256 :=
  σ.sload (vtiSlot σ v)

/-- **VTI-COHERENCE**: every decoded leaf key except 0 has a nonzero
`valueToIndex` entry.  The `key ≠ 0` carve-out is the genesis leaf:
`setup` seeds `leaves[0] = ⟨0,0,0⟩` but never writes `valueToIndex[0]`
(IndexedMerkleTree.sol:42-50), so key 0's vti entry is 0 along any real
history.  The dedup gate is unaffected: inserted values pass the
`insert_valueZero` guard (`V ≠ 0`), so the bridge below never needs key 0. -/
def VtiCoherent (σ : EVMState) : Prop :=
  ∀ L ∈ leafSetOf σ, L.key ≠ 0 → vtiAt σ L.key ≠ 0

/-! ### THE BRIDGE: the dedup-gate zero IS abstract freshness -/

/-- The dedup gate's threaded read transports to the entry state: the guards'
vti accessor runs ON the entry state (its slot is `vtiSlot evm V` by
definition), and a clean accessor is storage-transparent.  `hz` is verbatim
`insertGlue_prefix`'s dedup hypothesis. -/
theorem vti_entry_zero {evm : EVMState} {V : UInt256}
    (hclean : (accOut evm V 5).2.hash_collision = false)
    (hz : (accOut evm V 5).2.sload ((accOut evm V 5).1) = 0) :
    vtiAt evm V = 0 := by
  unfold vtiAt vtiSlot
  rw [← sload_accOut_of_clean ((accOut evm V 5).1) hclean]
  exact hz

/-- **THE FRESHNESS BRIDGE**: coherence + a zero vti entry + `V ≠ 0` give the
abstract key-freshness `V ∉ keys (leafSetOf evm)` — exactly the `hfresh`
residue of #68. -/
theorem hfresh_of_vtiCoherent {evm : EVMState} {V : UInt256}
    (hco : VtiCoherent evm) (hz : vtiAt evm V = 0) (hvnz : V ≠ 0) :
    V ∉ IMTAbstract.keys (leafSetOf evm) := by
  intro hmem
  unfold IMTAbstract.keys at hmem
  obtain ⟨L, hL, hLk⟩ := Finset.mem_image.mp hmem
  exact hco L hL (by rw [hLk]; exact hvnz) (by rw [hLk]; exact hz)

/-- The bridge composed with the gate pins, in `insertGlue_prefix`'s exact
hypothesis shapes: `hz` (dedup gate), `hvnz` (`insert_valueZero` guard,
selector 3172853053), and the guards-stage cleanliness. -/
theorem hfresh_of_dedup_gate {evm : EVMState} {V IX : UInt256}
    (hco : VtiCoherent evm)
    (hvnz : V ≠ 0)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    (hz : (accOut evm V 5).2.sload ((accOut evm V 5).1) = 0) :
    V ∉ IMTAbstract.keys (leafSetOf evm) :=
  hfresh_of_vtiCoherent hco
    (vti_entry_zero (accOut_clean_backward hcleanG) hz) hvnz

/-! ### The 32-byte-preimage separation discipline

Every storage write of the walk/pad/level-0 family lands at
`keccak(32-byte preimage) + small offset`.  A 64-byte-preimage keccak slot
(any mapping slot — base 4 or 5) is separated from ALL of them at once by
the preimage-length split.  `Sep32 s` packages that separation for a fixed
target slot `s`; the `_sep` walk frames below are the `_low` twins of
`imt_walk_discharge_user` with the low-slot axiom replaced by `Sep32`. -/

/-- `s` is missed by every 32-byte-preimage keccak slot at any small offset. -/
def Sep32 (s : UInt256) : Prop :=
  ∀ (σa σa' : EVMState) (p r j : UInt256),
    σa.keccak256 p 32 = some (r, σa') →
    j.val < Clear.KeccakInjective.lowSlotBound →
    r + j ≠ s

/-- Any 64-byte-preimage keccak slot satisfies `Sep32` (lengths 32 ≠ 64). -/
lemma sep32_of_keccak64 {σ σ' : EVMState} {p u : UInt256}
    (hk : σ.keccak256 p 64 = some (u, σ')) : Sep32 u := by
  intro σa σa' pa r j hpair hj
  exact Clear.KeccakInjective.keccak256_slot_sep hpair hk
    (Clear.KeccakInjective.mkInterval_ne_of_len_ne (by decide)) hj

/-- A `nodeStore` write misses a `Sep32` slot. -/
private lemma nodeStore_sload_sep
    {σ : EVMState} {base l j v s : UInt256}
    (hclean : (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).2.hash_collision = false)
    (hcleanA : (arrOut σ base).2.hash_collision = false)
    (hsep : Sep32 s)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound) :
    (nodeStore σ base l j v).sload s = σ.sload s := by
  unfold nodeStore
  have hksome := keccakOut_some_of_clean
    (σ := ((arrOut σ base).2.mstore 0 ((arrOut σ base).1 + l))) (p := 0) (n := 32)
    (by exact hclean)
  have hpair : ((arrOut σ base).2.mstore 0 ((arrOut σ base).1 + l)).keccak256 0 32
      = some ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).1,
              (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).2) := by
    rw [hksome]
    rfl
  have hne : (arrOut (arrOut σ base).2 ((arrOut σ base).1 + l)).1 + j ≠ s :=
    hsep _ _ _ _ _ hpair hj
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne)]
  rw [sload_arrOut_of_clean s hclean]
  rw [sload_arrOut_of_clean s hcleanA]

/-- The odd step misses a `Sep32` slot. -/
private lemma stepOdd_sload_sep
    {σ : EVMState} {base i idx cur s : UInt256}
    (hsep : Sep32 s)
    (hj : (Fin.shiftRight idx 1).val < Clear.KeccakInjective.lowSlotBound)
    (hfin : oddFinClean σ base i idx cur) :
    ((stepOdd σ base i idx cur).2).sload s = σ.sload s := by
  unfold oddFinClean at hfin
  have h4 := arrOut_clean_bwV hfin
  have h3 := arrOut_clean_bwV h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_bwV h2
  show (nodeStore (accOut (sibRead σ base i (idx - 1)).2
      (sibRead σ base i (idx - 1)).1 cur).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sibRead σ base i (idx - 1)).2 (sibRead σ base i (idx - 1)).1 cur).1).sload s
    = σ.sload s
  rw [nodeStore_sload_sep hfin h4 hsep hj]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]
  rw [sload_arrOut_of_clean s h1]

/-- The even step misses a `Sep32` slot. -/
private lemma stepEven_sload_sep
    {σ : EVMState} {base i idx cur s : UInt256}
    (hsep : Sep32 s)
    (hj : (Fin.shiftRight idx 1).val < Clear.KeccakInjective.lowSlotBound)
    (hfin : evenFinClean σ base i idx cur) :
    ((stepEven σ base i idx cur).2).sload s = σ.sload s := by
  unfold evenFinClean at hfin
  have h4 := arrOut_clean_bwV hfin
  have h3 := arrOut_clean_bwV h4
  have h2 := accOut_clean_backward h3
  have h1 := arrOut_clean_bwV h2
  show (nodeStore (accOut (sibRead σ base i (idx + 1)).2 cur
      (sibRead σ base i (idx + 1)).1).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sibRead σ base i (idx + 1)).2 cur (sibRead σ base i (idx + 1)).1).1).sload s
    = σ.sload s
  rw [nodeStore_sload_sep hfin h4 hsep hj]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut (arrOut σ base).2 ((arrOut σ base).1 + i)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]
  rw [sload_arrOut_of_clean s h1]

/-- The edge step misses a `Sep32` slot. -/
private lemma stepEdge_sload_sep
    {σ : EVMState} {ss base i idx cur s : UInt256}
    (hsep : Sep32 s)
    (hj : (Fin.shiftRight idx 1).val < Clear.KeccakInjective.lowSlotBound)
    (hfin : edgeFinClean σ ss base i idx cur) :
    ((stepEdge σ ss base i idx cur).2).sload s = σ.sload s := by
  unfold edgeFinClean at hfin
  have h4 := arrOut_clean_bwV hfin
  have h3 := arrOut_clean_bwV h4
  have h2 := accOut_clean_backward h3
  show (nodeStore (accOut (sideRead σ (ss + 3) i).2 cur
      (sideRead σ (ss + 3) i).1).2 base (i + 1) (Fin.shiftRight idx 1)
      (accOut (sideRead σ (ss + 3) i).2 cur (sideRead σ (ss + 3) i).1).1).sload s
    = σ.sload s
  rw [nodeStore_sload_sep hfin h4 hsep hj]
  rw [sload_accOut_of_clean s h3]
  show ((arrOut σ (ss + 3)).2).sload s = σ.sload s
  rw [sload_arrOut_of_clean s h2]

/-- The dispatched walk step misses a `Sep32` slot. -/
private lemma updateStep_sload_sep
    {σ : EVMState} {ss base i idx maxN cur s : UInt256}
    (hsep : Sep32 s)
    (hok : StepLowOK ss base (σ, i, idx, maxN, cur)) :
    ((updateStep σ ss base i idx maxN cur).2).sload s = σ.sload s := by
  obtain ⟨hj, hflag⟩ := hok
  unfold updateStep
  by_cases hpar : Fin.land idx 1 = 0
  · by_cases hedge : maxN = idx
    · rw [if_pos hpar, if_pos hedge]
      rw [if_pos hpar, if_pos hedge] at hflag
      exact stepEdge_sload_sep hsep hj hflag
    · rw [if_pos hpar, if_neg hedge]
      rw [if_pos hpar, if_neg hedge] at hflag
      exact stepEven_sload_sep hsep hj hflag
  · rw [if_neg hpar]
    rw [if_neg hpar] at hflag
    exact stepOdd_sload_sep hsep hj hflag

/-- **The Merkle walk misses every `Sep32` slot** (the `updateWalk_sload_low`
twin for keccak-slot targets). -/
lemma updateWalk_sload_sep :
    ∀ (kk : ℕ) {σ : EVMState} {ss base i idx maxN cur s : UInt256},
    Sep32 s →
    (∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i idx maxN cur)) →
    ((updateWalk ss base kk σ i idx maxN cur).1).sload s = σ.sload s := by
  intro kk
  induction kk with
  | zero =>
    intro σ ss base i idx maxN cur s _ _
    rfl
  | succ kk ih =>
    intro σ ss base i idx maxN cur s hsep hok
    have h0 := hok 0 (by omega)
    simp only [updateWalk] at h0 ⊢
    rw [ih hsep (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [updateWalk] using this)]
    exact updateStep_sload_sep hsep h0

/-- The padding step misses a `Sep32` slot. -/
private lemma padStep_sload_sep
    {σ : EVMState} {i s : UInt256}
    (hsep : Sep32 s)
    (hi : i.val < Clear.KeccakInjective.lowSlotBound)
    (hlen : (((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i)).val
      < Clear.KeccakInjective.lowSlotBound)
    (hfin : padFinClean σ i) :
    ((padStep σ i).sload s) = σ.sload s := by
  unfold padFinClean at hfin
  have hE1 : (((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))).hash_collision
        = false :=
    arrOut_clean_bwV hfin
  have hB : ((arrOut (arrOut σ 2).2 3).2).hash_collision = false := by
    rwa [hash_collision_sstoreV] at hE1
  have hA : ((arrOut σ 2).2).hash_collision = false := arrOut_clean_bwV hB
  have hpairFin := arrOut_pairV hfin
  have hpairA := arrOut_pairV hA
  have hne1 : (arrOut ((arrOut (arrOut σ 2).2 3).2.sstore ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut σ 2).1 + i) + 1))
      ((arrOut σ 2).1 + i)).1
      + ((arrOut (arrOut σ 2).2 3).2).sload ((arrOut σ 2).1 + i) ≠ s :=
    hsep _ _ _ _ _ hpairFin hlen
  have hne2 : (arrOut σ 2).1 + i ≠ s :=
    hsep _ _ _ _ _ hpairA hi
  show ((pushEvm (arrOut (arrOut σ 2).2 3).2 ((arrOut σ 2).1 + i)
      ((arrOut (arrOut σ 2).2 3).2.sload ((arrOut (arrOut σ 2).2 3).1 + i))).sload s)
    = σ.sload s
  unfold pushEvm
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne1)]
  rw [sload_arrOut_of_clean s hfin]
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne2)]
  rw [sload_arrOut_of_clean s hB]
  rw [sload_arrOut_of_clean s hA]

/-- **The padding walk misses every `Sep32` slot** (the `padWalk_sload_low`
twin). -/
lemma padWalk_sload_sep :
    ∀ (kk : ℕ) {σ : EVMState} {i om m s : UInt256},
    Sep32 s →
    (∀ j, j < kk → PadLowOK (padWalk j σ i om m)) →
    ((padWalk kk σ i om m).1).sload s = σ.sload s := by
  intro kk
  induction kk with
  | zero =>
    intro σ i om m s _ _
    rfl
  | succ kk ih =>
    intro σ i om m s hsep hok
    have h0 := hok 0 (by omega)
    simp only [padWalk] at h0 ⊢
    rw [ih hsep (by
      intro j hj
      have := hok (j+1) (by omega)
      simpa only [padWalk] using this)]
    exact padStep_sload_sep hsep h0.1 h0.2.1 h0.2.2

/-! ### The push-tail composites (count bump → pad → level-0 write → walk) -/

/-- The whole push tail (bump, pad walk, level-0 write, root walk) misses
every `Sep32` slot off slot 1. -/
private lemma pushOut_sload_sep {E : EVMState} {P s : UInt256} {kp kk : ℕ}
    (hsep : Sep32 s) (h1s : (1 : UInt256) ≠ s)
    (hA1 : (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).2.hash_collision = false)
    (hA2 : (arrOut (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).2
        (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hnidx : ((pushEH E P).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (hokp : ∀ j, j < kp → PadLowOK (pushPadW E P j))
    (hok₂ : ∀ j, j < kk → StepLowOK 0 ((0 : UInt256) + 2) (pushOutW E P kp j)) :
    (pushOutW E P kp kk).1.sload s = (pushEH E P).sload s := by
  have h1 : (pushOutW E P kp kk).1.sload s
      = (leafWriteEvm (pushPadW E P kp).1 0 ((pushEH E P).sload 1) (pushHL E P)).sload s :=
    updateWalk_sload_sep kk hsep hok₂
  have h2 : (leafWriteEvm (pushPadW E P kp).1 0 ((pushEH E P).sload 1) (pushHL E P)).sload s
      = (pushPadW E P kp).1.sload s :=
    leafWrite_sload_neV hA1 hA2 (hsep _ _ _ _ _ (arrOut_pairV hA2) hnidx)
  have h3 : (pushPadW E P kp).1.sload s
      = ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)).sload s :=
    padWalk_sload_sep kp hsep hokp
  have h4 : ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)).sload s
      = (pushEH E P).sload s := sload_sstore_ne h1s
  rw [h1, h2, h3, h4]

/-- The push tail preserves the junk window (bytes ≥ 64). -/
private lemma pushOut_junk {E : EVMState} {P : UInt256} {kp kk : ℕ} {b : UInt256}
    (hb : 64 ≤ b.val) :
    Finmap.lookup b (pushOutW E P kp kk).1.machine_state.memory
      = Finmap.lookup b (pushEH E P).machine_state.memory := by
  have h1 : Finmap.lookup b (pushOutW E P kp kk).1.machine_state.memory
      = Finmap.lookup b (leafWriteEvm (pushPadW E P kp).1 0
          ((pushEH E P).sload 1) (pushHL E P)).machine_state.memory :=
    updateWalk_junk kk hb
  have h2 : Finmap.lookup b (leafWriteEvm (pushPadW E P kp).1 0
      ((pushEH E P).sload 1) (pushHL E P)).machine_state.memory
      = Finmap.lookup b (pushPadW E P kp).1.machine_state.memory := by
    unfold leafWriteEvm
    rw [machine_state_sstoreV, arrOut_junkV hb, arrOut_junkV hb]
  have h3 : Finmap.lookup b (pushPadW E P kp).1.machine_state.memory
      = Finmap.lookup b ((pushEH E P).sstore 1
          ((pushEH E P).sload 1 + 1)).machine_state.memory :=
    padWalk_junk kp hb
  have h4 : Finmap.lookup b ((pushEH E P).sstore 1
      ((pushEH E P).sload 1 + 1)).machine_state.memory
      = Finmap.lookup b (pushEH E P).machine_state.memory := by
    rw [machine_state_sstoreV]
  rw [h1, h2, h3, h4]

/-- The push tail only grows the keccak cache. -/
private lemma pushOut_mono {E : EVMState} {P : UInt256} {kp kk : ℕ}
    {I : List UInt256} {u : UInt256}
    (hI : Finmap.lookup I (pushEH E P).keccak_map = some u) :
    Finmap.lookup I (pushOutW E P kp kk).1.keccak_map = some u := by
  refine updateWalk_lookup_mono kk ?_
  show Finmap.lookup I (leafWriteEvm (pushPadW E P kp).1 0
      ((pushEH E P).sload 1) (pushHL E P)).keccak_map = some u
  unfold leafWriteEvm
  rw [keccak_map_sstoreV]
  refine arrOut_monoV (arrOut_monoV ?_)
  refine padWalk_lookup_mono kp ?_
  rw [keccak_map_sstoreV]
  exact hI

/-- An `H3`-anchored cached vti word pins the FINAL state's vti slot: the
push tail preserves the junk window (interval equality) and the cache. -/
private lemma vtiSlot_pushOut {E : EVMState} {P x u : UInt256} {kp kk : ℕ}
    (hcu : Finmap.lookup (accInterval (pushEH E P) x 5)
        (pushEH E P).keccak_map = some u) :
    vtiSlot (pushOutW E P kp kk).1 x = u := by
  have hInt : accInterval (pushOutW E P kp kk).1 x 5
      = accInterval (pushEH E P) x 5 :=
    accInterval_eq (fun b hb1 _ => pushOut_junk hb1)
  have hc : Finmap.lookup (accInterval (pushOutW E P kp kk).1 x 5)
      (pushOutW E P kp kk).1.keccak_map = some u := by
    rw [hInt]
    exact pushOut_mono hcu
  exact (vtiSlot_keccakV hc).2

/-! ### PRESERVATION, per slot -/

open Clear.KeccakDeterminism in
/-- **Old keys' vti entries survive the whole insert chain**: for `x ≠ V`
with its vti word cached at the entry and `H3` anchors, the final state's
`valueToIndex[x]` read equals the entry state's.  Write inventory: the two
base-4 struct copies (word-32 preimage split), the vti write at `V` (word-0
split, keccak injectivity), the two `hashLeaf` steps (no `sstore`), the
level-0 writes and both walks (32-vs-64 length split), the count bump (low
slot). -/
theorem vtiAt_wFinal_old
    {evm : EVMState} {V IX x u : UInt256} {k k2 k3 : ℕ}
    (hxV : x ≠ V)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    (hclean4 : (accOut (wE4 evm V IX) IX 4).2.hash_collision = false)
    (hcleanF : (accOut (wF4 evm V IX k) (evm.sload 1) 4).2.hash_collision = false)
    (hcleanV : (accOut (wF5 evm V IX k) V 5).2.hash_collision = false)
    (hcleanH1 : (wH1 evm V IX).hash_collision = false)
    (hcleanH3 : (wH3 evm V IX k).hash_collision = false)
    (hcleanB1 : (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanB2 : (arrOut (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).2
        (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hcleanA1 : (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanA2 : (arrOut (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2
        (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j))
    -- the two-anchor vti cache pack for `x`
    (hcu : Finmap.lookup (accInterval evm x 5) evm.keccak_map = some u)
    (hcuH : Finmap.lookup (accInterval (wH3 evm V IX k) x 5)
        (wH3 evm V IX k).keccak_map = some u) :
    vtiAt (wFinal evm V IX k k2 k3) x = vtiAt evm x := by
  -- the entry-anchor keccak witness for `u`
  have hku := (vtiSlot_keccakV hcu).1
  have hvu : vtiSlot evm x = u := (vtiSlot_keccakV hcu).2
  have hsep : Sep32 u := sep32_of_keccak64 hku
  have h1u : (1 : UInt256) ≠ u :=
    Ne.symm (Clear.KeccakInjective.keccak256_ne_lowSlot 1 hku (by decide))
  -- base-4 copy-slot witnesses (thread-stable accessor caches)
  have hkE := (leafSlot_keccak (cached_accThread hclean4)).1
  have hkF := (leafSlot_keccak (cached_accThread hcleanF)).1
  have hE0 : (accOut (wE4 evm V IX) IX 4).1 ≠ u := by
    have h := Clear.KeccakInjective.keccak256_slot_sep (i := 0) hkE hku
      (Ne.symm base54_interval_neV) (by decide)
    simpa using h
  have hE1 : (accOut (wE4 evm V IX) IX 4).1 + 1 ≠ u :=
    Clear.KeccakInjective.keccak256_slot_sep (i := 1) hkE hku
      (Ne.symm base54_interval_neV) (by decide)
  have hE2 : (accOut (wE4 evm V IX) IX 4).1 + 2 ≠ u :=
    Clear.KeccakInjective.keccak256_slot_sep (i := 2) hkE hku
      (Ne.symm base54_interval_neV) (by decide)
  have hF0 : (accOut (wF4 evm V IX k) (evm.sload 1) 4).1 ≠ u := by
    have h := Clear.KeccakInjective.keccak256_slot_sep (i := 0) hkF hku
      (Ne.symm base54_interval_neV) (by decide)
    simpa using h
  have hF1 : (accOut (wF4 evm V IX k) (evm.sload 1) 4).1 + 1 ≠ u :=
    Clear.KeccakInjective.keccak256_slot_sep (i := 1) hkF hku
      (Ne.symm base54_interval_neV) (by decide)
  have hF2 : (accOut (wF4 evm V IX k) (evm.sload 1) 4).1 + 2 ≠ u :=
    Clear.KeccakInjective.keccak256_slot_sep (i := 2) hkF hku
      (Ne.symm base54_interval_neV) (by decide)
  -- the vti write slot (base 5, key V ≠ x — keccak injectivity, word 0)
  have hcvPost : Finmap.lookup (accInterval ((accOut (wF5 evm V IX k) V 5).2) V 5)
      ((accOut (wF5 evm V IX k) V 5).2).keccak_map
      = some ((accOut (wF5 evm V IX k) V 5).1) := by
    rw [show accInterval ((accOut (wF5 evm V IX k) V 5).2) V 5
        = accInterval (wF5 evm V IX k) V 5 from
      accInterval_eq (fun b hb1 _ => accOut_junk_window hb1)]
    exact accOut_caches_of_clean hcleanV
  have hkSLV := (vtiSlot_keccakV hcvPost).1
  have hSLVne : (accOut (wF5 evm V IX k) V 5).1 ≠ u :=
    Clear.KeccakInjective.keccak256_inj hkSLV hku (vtiInterval_neV (Ne.symm hxV))
  -- the final-state slot pin (H3 anchor + junk frame + cache monotonicity)
  have hslotF : vtiSlot (wFinal evm V IX k k2 k3) x = u :=
    vtiSlot_pushOut (E := wS3 evm V IX k) (P := (wS2 evm V IX k).mload 64)
      (kp := k2) (kk := k3) hcuH
  -- assemble
  show (wFinal evm V IX k k2 k3).sload (vtiSlot (wFinal evm V IX k k2 k3) x)
      = evm.sload (vtiSlot evm x)
  rw [hslotF, hvu]
  calc (wFinal evm V IX k k2 k3).sload u
      = (wH3 evm V IX k).sload u :=
        pushOut_sload_sep hsep h1u hcleanA1 hcleanA2 hnidx hokp hok₂
    _ = (wS3 evm V IX k).sload u := sload_hashLeafOut_of_clean u hcleanH3
    _ = ((accOut (wF5 evm V IX k) V 5).2).sload u := sload_sstore_ne hSLVne
    _ = (wF5 evm V IX k).sload u := sload_accOut_of_clean u hcleanV
    _ = (wF4 evm V IX k).sload u := copyChain_sload_neV hcleanF hF0 hF1 hF2
    _ = (wS2 evm V IX k).sload u := rfl
    _ = (leafWriteEvm (wH1 evm V IX) 0 IX
          (hashLeafOut (wS1 evm V IX) ((guardsEvm evm V IX).mload 64)).1).sload u :=
        updateWalk_sload_sep k hsep hok₁
    _ = (wH1 evm V IX).sload u :=
        leafWrite_sload_neV hcleanB1 hcleanB2
          (hsep _ _ _ _ _ (arrOut_pairV hcleanB2) hIXlow)
    _ = (wS1 evm V IX).sload u := sload_hashLeafOut_of_clean u hcleanH1
    _ = (wE4 evm V IX).sload u := copyChain_sload_neV hclean4 hE0 hE1 hE2
    _ = (guardsEvm evm V IX).sload u := rfl
    _ = evm.sload u := guards_sload hcleanG u

open Clear.KeccakDeterminism in
/-- **`V`'s final vti entry is the old count**: the S3 registration writes
`NI = evm.sload 1` at `valueToIndex[V]`, and the push tail preserves both
the value and (via the H3-anchored cached word, tied to the write-site F5
anchor by lookup functionality) the slot. -/
theorem vtiAt_wFinal_V
    {evm : EVMState} {V IX wv : UInt256} {k k2 k3 : ℕ}
    (hcleanV : (accOut (wF5 evm V IX k) V 5).2.hash_collision = false)
    (hcleanH3 : (wH3 evm V IX k).hash_collision = false)
    (hcleanA1 : (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanA2 : (arrOut (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2
        (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (haccV : (((accOut (wF5 evm V IX k) V 5).2).lookupAccount
        ((accOut (wF5 evm V IX k) V 5).2).execution_env.code_owner).isSome)
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j))
    -- the two-anchor vti cache pack for `V` (write-site F5 + H3)
    (hcvF : Finmap.lookup (accInterval (wF5 evm V IX k) V 5)
        (wF5 evm V IX k).keccak_map = some wv)
    (hcvH : Finmap.lookup (accInterval (wH3 evm V IX k) V 5)
        (wH3 evm V IX k).keccak_map = some wv) :
    vtiAt (wFinal evm V IX k k2 k3) V = evm.sload 1 := by
  -- functionality at the F5 anchor: the pack word IS the write slot
  have htrans : Finmap.lookup (accInterval (wF5 evm V IX k) V 5)
      ((accOut (wF5 evm V IX k) V 5).2).keccak_map = some wv :=
    accOut_lookup_mono hcvF
  have hpost : Finmap.lookup (accInterval (wF5 evm V IX k) V 5)
      ((accOut (wF5 evm V IX k) V 5).2).keccak_map
      = some ((accOut (wF5 evm V IX k) V 5).1) :=
    accOut_caches_of_clean hcleanV
  have hwv : wv = (accOut (wF5 evm V IX k) V 5).1 :=
    Option.some.inj (htrans.symm.trans hpost)
  -- the write-slot keccak witness → Sep32 + low-slot separation
  have hcvPost : Finmap.lookup (accInterval ((accOut (wF5 evm V IX k) V 5).2) V 5)
      ((accOut (wF5 evm V IX k) V 5).2).keccak_map
      = some ((accOut (wF5 evm V IX k) V 5).1) := by
    rw [show accInterval ((accOut (wF5 evm V IX k) V 5).2) V 5
        = accInterval (wF5 evm V IX k) V 5 from
      accInterval_eq (fun b hb1 _ => accOut_junk_window hb1)]
    exact accOut_caches_of_clean hcleanV
  have hkSLV := (vtiSlot_keccakV hcvPost).1
  have hsepV : Sep32 ((accOut (wF5 evm V IX k) V 5).1) := sep32_of_keccak64 hkSLV
  have h1V : (1 : UInt256) ≠ (accOut (wF5 evm V IX k) V 5).1 :=
    Ne.symm (Clear.KeccakInjective.keccak256_ne_lowSlot 1 hkSLV (by decide))
  -- the final-state slot pin
  have hslotF : vtiSlot (wFinal evm V IX k k2 k3) V
      = (accOut (wF5 evm V IX k) V 5).1 :=
    (vtiSlot_pushOut (E := wS3 evm V IX k) (P := (wS2 evm V IX k).mload 64)
      (kp := k2) (kk := k3) hcvH).trans hwv
  -- assemble
  show (wFinal evm V IX k k2 k3).sload (vtiSlot (wFinal evm V IX k k2 k3) V)
      = evm.sload 1
  rw [hslotF]
  calc (wFinal evm V IX k k2 k3).sload ((accOut (wF5 evm V IX k) V 5).1)
      = (wH3 evm V IX k).sload ((accOut (wF5 evm V IX k) V 5).1) :=
        pushOut_sload_sep hsepV h1V hcleanA1 hcleanA2 hnidx hokp hok₂
    _ = (wS3 evm V IX k).sload ((accOut (wF5 evm V IX k) V 5).1) :=
        sload_hashLeafOut_of_clean _ hcleanH3
    _ = evm.sload 1 := sload_sstore_self haccV

/-! ### The abstract key-set corollary of `imtInsert` -/

/-- Every key of the inserted set is `v` or an old key (`imtInsert` erases
the window leaf but re-adds its KEY, retargeted). -/
private lemma mem_imtInsert_key {s : Finset AbsLeaf} {W₀ L : AbsLeaf} {v : UInt256}
    (hW : W₀ ∈ s) (hL : L ∈ imtInsert s W₀ v) :
    L.key = v ∨ ∃ L', L' ∈ s ∧ L'.key = L.key := by
  unfold imtInsert at hL
  rcases Finset.mem_insert.mp hL with h1 | hL2
  · subst h1
    exact Or.inr ⟨W₀, hW, rfl⟩
  · rcases Finset.mem_insert.mp hL2 with h2 | hL3
    · subst h2
      exact Or.inl rfl
    · exact Or.inr ⟨L, Finset.mem_of_mem_erase hL3, rfl⟩

/-! ### PRESERVATION -/

open Clear.KeccakDeterminism in
/-- **VTI-COHERENCE IS PRESERVED by the deployed insert** (#69).  Under the
weld surface (which gives `leafSetOf (wFinal …) = imtInsert …`) plus the vti
cache pack, the invariant transports: old keys' entries are untouched
(`vtiAt_wFinal_old`), and `V`'s new entry is the old count, nonzero by the
glue's own initialized guard `h1nz` (genesis seeds leaf 0, so the count is
≥ 1 along any real history — and the dispatcher reverts otherwise). -/
theorem vtiCoherent_preserved
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    (hco : VtiCoherent evm)
    (hVfresh : V ∉ IMTAbstract.keys (leafSetOf evm))
    (h1nz : evm.sload 1 ≠ 0)
    -- ===== the weld surface (verbatim `insertGlue_leafSetOf`) =====
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowW : 96 ≤ ((guardsEvm evm V IX).mload 64).val)
    (hpN : ((wS2 evm V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowN : 96 ≤ ((wS2 evm V IX k).mload 64).val)
    (hclean4 : (accOut (wE4 evm V IX) IX 4).2.hash_collision = false)
    (hcleanF : (accOut (wF4 evm V IX k) (evm.sload 1) 4).2.hash_collision = false)
    (hcleanV : (accOut (wF5 evm V IX k) V 5).2.hash_collision = false)
    (hcleanH1 : (wH1 evm V IX).hash_collision = false)
    (hcleanH3 : (wH3 evm V IX k).hash_collision = false)
    (hcleanB1 : (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanB2 : (arrOut (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).2
        (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hcleanA1 : (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanA2 : (arrOut (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2
        (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (haccEK : (((accOut (wE4 evm V IX) IX 4).2).lookupAccount
        ((accOut (wE4 evm V IX) IX 4).2).execution_env.code_owner).isSome)
    (haccFK : (((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).lookupAccount
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).execution_env.code_owner).isSome)
    (haccH3 : ((wH3 evm V IX k).lookupAccount
        (wH3 evm V IX k).execution_env.code_owner).isSome)
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (hcach : ∀ m : ℕ, m ≤ (evm.sload 1).val → ∃ wm,
      Finmap.lookup (accInterval evm (m : UInt256) 4) evm.keccak_map = some wm
      ∧ Finmap.lookup (accInterval (guardsEvm evm V IX) (m : UInt256) 4)
          (guardsEvm evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wE4 evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wF4 evm V IX k) (m : UInt256) 4)
          (wF4 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm)
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j))
    -- ===== the vti pack =====
    (haccV : (((accOut (wF5 evm V IX k) V 5).2).lookupAccount
        ((accOut (wF5 evm V IX k) V 5).2).execution_env.code_owner).isSome)
    (hvtiV : ∃ wv, Finmap.lookup (accInterval (wF5 evm V IX k) V 5)
        (wF5 evm V IX k).keccak_map = some wv
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) V 5)
          (wH3 evm V IX k).keccak_map = some wv)
    (hvtiOld : ∀ L ∈ leafSetOf evm, L.key ≠ 0 → ∃ u,
      Finmap.lookup (accInterval evm L.key 5) evm.keccak_map = some u
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) L.key 5)
          (wH3 evm V IX k).keccak_map = some u) :
    VtiCoherent (wFinal evm V IX k k2 k3) := by
  have hset := insertGlue_leafSetOf hbound hnw hcleanG hpG hpW hplowW hpN hplowN
    hclean4 hcleanF hcleanV hcleanH1 hcleanH3 hcleanB1 hcleanB2 hcleanA1
    hcleanA2 haccEK haccFK haccH3 hIXlow hnidx hcach hinj hok₁ hokp hok₂
  have hwlt : IX.val < (evm.sload 1).val := hbound
  have hW₀ : decodeLeaf evm IX ∈ leafSetOf evm := by
    unfold leafSetOf
    exact Finset.mem_image.mpr
      ⟨IX.val, Finset.mem_range.mpr hwlt, by rw [Fin.cast_val_eq_self]⟩
  intro L hL hLnz
  rw [hset] at hL
  rcases mem_imtInsert_key hW₀ hL with hkeyV | ⟨L', hL', hLk⟩
  · -- the new key V: its entry is the old count, nonzero by the init guard
    rw [hkeyV]
    obtain ⟨wv, hcvF, hcvH⟩ := hvtiV
    rw [vtiAt_wFinal_V hcleanV hcleanH3 hcleanA1 hcleanA2 hnidx haccV
      hokp hok₂ hcvF hcvH]
    exact h1nz
  · -- an old key: its vti slot is untouched by the whole chain
    have hknz : L'.key ≠ 0 := by rw [hLk]; exact hLnz
    have hxV : L.key ≠ V := by
      intro h
      apply hVfresh
      unfold IMTAbstract.keys
      exact Finset.mem_image.mpr ⟨L', hL', by rw [hLk, h]⟩
    obtain ⟨u, hcu, hcuH⟩ := hvtiOld L' hL' hknz
    rw [hLk] at hcu hcuH
    rw [vtiAt_wFinal_old hxV hcleanG hclean4 hcleanF hcleanV hcleanH1 hcleanH3
      hcleanB1 hcleanB2 hcleanA1 hcleanA2 hIXlow hnidx hok₁ hokp hok₂ hcu hcuH]
    have h := hco L' hL' hknz
    rw [hLk] at h
    exact h

/-! ### THE CLOSED CAPSTONE -/

open Clear.KeccakDeterminism in
/-- **THE EVOLUTION PACKAGING, CLOSED (#69)** — `insertGlue_evolution_step`
with the `hfresh` residue REPLACED by the storage invariant: under
`VtiCoherent evm`, the contract's own gate pins (`hz` — the dedup gate;
`hvnz` — the `insert_valueZero` guard; `h1nz` — the initialized guard,
count ≥ 1), the weld surface and the vti cache pack, the dispatcher's pass
state is a WITNESSED abstract `Evolution` insert step AND the invariant
holds again at the post-state.  Invariant in, invariant out — the theorem
is self-sustaining along any history whose genesis satisfies `VtiCoherent`
(the freshly-`setup` tree does: its only leaf has key 0, carved out). -/
theorem insertGlue_evolution_closed
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    -- THE INVARIANT (in)
    (hco : VtiCoherent evm)
    -- the contract's own gate pins (verbatim `insertGlue_prefix` shapes)
    (h1nz : evm.sload 1 ≠ 0)
    (hvnz : V ≠ 0)
    (hz : (accOut evm V 5).2.sload ((accOut evm V 5).1) = 0)
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    (hvo : (guardsEvm evm V IX).mload (guardsLM evm V IX) < V)
    (hwin : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64) = 0
        ∨ ¬ ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64) < V))
    -- the abstract list well-formedness (free along history, #68 header)
    (hclosed : NextClosed (leafSetOf evm))
    -- ===== the weld surface =====
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowW : 96 ≤ ((guardsEvm evm V IX).mload 64).val)
    (hpN : ((wS2 evm V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowN : 96 ≤ ((wS2 evm V IX k).mload 64).val)
    (hclean4 : (accOut (wE4 evm V IX) IX 4).2.hash_collision = false)
    (hcleanF : (accOut (wF4 evm V IX k) (evm.sload 1) 4).2.hash_collision = false)
    (hcleanV : (accOut (wF5 evm V IX k) V 5).2.hash_collision = false)
    (hcleanH1 : (wH1 evm V IX).hash_collision = false)
    (hcleanH3 : (wH3 evm V IX k).hash_collision = false)
    (hcleanB1 : (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanB2 : (arrOut (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).2
        (arrOut (wH1 evm V IX) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hcleanA1 : (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanA2 : (arrOut (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2
        (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (haccEK : (((accOut (wE4 evm V IX) IX 4).2).lookupAccount
        ((accOut (wE4 evm V IX) IX 4).2).execution_env.code_owner).isSome)
    (haccFK : (((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).lookupAccount
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).execution_env.code_owner).isSome)
    (haccH3 : ((wH3 evm V IX k).lookupAccount
        (wH3 evm V IX k).execution_env.code_owner).isSome)
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (hcach : ∀ m : ℕ, m ≤ (evm.sload 1).val → ∃ wm,
      Finmap.lookup (accInterval evm (m : UInt256) 4) evm.keccak_map = some wm
      ∧ Finmap.lookup (accInterval (guardsEvm evm V IX) (m : UInt256) 4)
          (guardsEvm evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wE4 evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wF4 evm V IX k) (m : UInt256) 4)
          (wF4 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm)
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j))
    -- ===== the vti pack =====
    (haccV : (((accOut (wF5 evm V IX k) V 5).2).lookupAccount
        ((accOut (wF5 evm V IX k) V 5).2).execution_env.code_owner).isSome)
    (hvtiV : ∃ wv, Finmap.lookup (accInterval (wF5 evm V IX k) V 5)
        (wF5 evm V IX k).keccak_map = some wv
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) V 5)
          (wH3 evm V IX k).keccak_map = some wv)
    (hvtiOld : ∀ L ∈ leafSetOf evm, L.key ≠ 0 → ∃ u,
      Finmap.lookup (accInterval evm L.key 5) evm.keccak_map = some u
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) L.key 5)
          (wH3 evm V IX k).keccak_map = some u) :
    (∃ W₀ v', W₀ ∈ leafSetOf evm ∧ W₀.key < v'
      ∧ (W₀.nextKey = 0 ∨ v' < W₀.nextKey)
      ∧ leafSetOf (wFinal evm V IX k k2 k3)
          = imtInsert (leafSetOf evm) W₀ v')
    ∧ VtiCoherent (wFinal evm V IX k k2 k3) := by
  -- the freshness residue of #68, DERIVED from the invariant + the gate pin
  have hfresh : V ∉ IMTAbstract.keys (leafSetOf evm) :=
    hfresh_of_dedup_gate hco hvnz hcleanG hz
  refine ⟨insertGlue_evolution_step hbound hnw hvo hwin hclosed hfresh hcleanG
    hpG hpW hplowW hpN hplowN hclean4 hcleanF hcleanV hcleanH1 hcleanH3
    hcleanB1 hcleanB2 hcleanA1 hcleanA2 haccEK haccFK haccH3 hIXlow hnidx
    hcach hinj hok₁ hokp hok₂, ?_⟩
  exact vtiCoherent_preserved hco hfresh h1nz hbound hnw hcleanG hpG hpW
    hplowW hpN hplowN hclean4 hcleanF hcleanV hcleanH1 hcleanH3 hcleanB1
    hcleanB2 hcleanA1 hcleanA2 haccEK haccFK haccH3 hIXlow hnidx hcach hinj
    hok₁ hokp hok₂ haccV hvtiV hvtiOld


/-! ## The vti frames on the derived route

`Sep32` quantifies over an ARBITRARY state's 32-byte hash, so no pool invariant reaches it --
the other state need not share a pool at all.  Its only producer, `sep32_of_keccak64`, is
therefore irreducibly `keccak256_slot_sep`.

The cached-slot walk family (`imt_fidelity`) is the reachable form of the same fact: it
separates a MINTED array base from a slot cached as a 64-byte hash IN THE SAME POOL.  Every
use of `Sep32` under `vtiAt_wFinal_*` is of that shape -- the 32-byte hashes are the push
tail's own `arrOut`s, downstream of the entry -- so each has a derived companion here. -/

/-- `arrOut` preserves existing cache entries (local copy of `imt_fidelity`'s private one). -/
private lemma arrOut_mono_V {σ : EVMState} {a : UInt256}
    {I : List UInt256} {w : UInt256}
    (hI : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (arrOut σ a).2.keccak_map = some w := by
  unfold arrOut
  exact keccakOut_lookup_mono (by rw [keccak_map_mstore]; exact hI)

/-- **DERIVED** companion to `pushOut_sload_sep`: the push tail leaves a cached 64-byte slot
(plus a small offset) exactly where it found it. -/
lemma pushOut_sload_cached_of_config
    {E : EVMState} {ms : MachineState} {P q w k : UInt256} {kp kk : ℕ}
    (hsepH : Clear.KeccakSlotSep.Separated (pushEH E P))
    (husedH : Clear.KeccakFresh.CacheInUsed (pushEH E P))
    (hinjH : Clear.KeccakFresh.CacheInj (pushEH E P))
    (hcw : Finmap.lookup (mkInterval ms q 64) (pushEH E P).keccak_map = some w)
    (hk : k.val < Clear.KeccakInjective.lowSlotBound)
    (h1s : (1 : UInt256) ≠ w + k)
    (hA1 : (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).2.hash_collision = false)
    (hA2 : (arrOut (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).2
        (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hnidx : ((pushEH E P).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (hokp : ∀ j, j < kp → PadLowOK (pushPadW E P j))
    (hok₂ : ∀ j, j < kk → StepLowOK 0 ((0 : UInt256) + 2) (pushOutW E P kp j)) :
    (pushOutW E P kp kk).1.sload (w + k) = (pushEH E P).sload (w + k) := by
  -- the pool triple along the push tail
  have hsepB : Clear.KeccakSlotSep.Separated
      ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)) :=
    Clear.StorageFrame.separated_sstore hsepH
  have husedB : Clear.KeccakFresh.CacheInUsed
      ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)) :=
    Clear.StorageFrame.cacheInUsed_sstore husedH
  have hinjB : Clear.KeccakFresh.CacheInj
      ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)) :=
    Clear.StorageFrame.cacheInj_sstore hinjH
  have hsepP : Clear.KeccakSlotSep.Separated (pushPadW E P kp).1 :=
    separated_padWalk kp hsepB
  have husedP : Clear.KeccakFresh.CacheInUsed (pushPadW E P kp).1 :=
    cacheInUsed_padWalk kp husedB
  have hinjP : Clear.KeccakFresh.CacheInj (pushPadW E P kp).1 :=
    cacheInj_padWalk kp husedB hinjB
  -- the cache hit along the same chain
  have hcB : Finmap.lookup (mkInterval ms q 64)
      ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)).keccak_map = some w := by
    rw [keccak_map_sstoreV]; exact hcw
  have hcP : Finmap.lookup (mkInterval ms q 64) ((pushPadW E P kp).1).keccak_map = some w :=
    padWalk_lookup_mono kp hcB
  have hcW : Finmap.lookup (mkInterval ms q 64)
      (leafWriteEvm (pushPadW E P kp).1 0 ((pushEH E P).sload 1) (pushHL E P)).keccak_map
        = some w := by
    unfold leafWriteEvm
    rw [keccak_map_sstoreV]
    exact arrOut_mono_V (arrOut_mono_V hcP)
  -- the four steps of the tail
  have h1 : (pushOutW E P kp kk).1.sload (w + k)
      = (leafWriteEvm (pushPadW E P kp).1 0 ((pushEH E P).sload 1) (pushHL E P)).sload
          (w + k) :=
    updateWalk_sload_cached_of_config kk
      (separated_leafWriteEvm hsepP) (cacheInUsed_leafWriteEvm husedP)
      (cacheInj_leafWriteEvm husedP hinjP) hcW hk hok₂
  have h2 : (leafWriteEvm (pushPadW E P kp).1 0 ((pushEH E P).sload 1) (pushHL E P)).sload
        (w + k)
      = (pushPadW E P kp).1.sload (w + k) :=
    leafWrite_sload_neV hA1 hA2
      (arrSlot_ne_cached64_of_clean (ms := ms) (q := q)
        (separated_arrOut (separated_arrOut hsepP))
        (cacheInj_arrOut (cacheInUsed_arrOut husedP) (cacheInj_arrOut husedP hinjP))
        hA2 (arrOut_mono_V hcP) hnidx hk)
  have h3 : (pushPadW E P kp).1.sload (w + k)
      = ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)).sload (w + k) :=
    padWalk_sload_cached_of_config kp hsepB husedB hinjB hcB hk hokp
  have h4 : ((pushEH E P).sstore 1 ((pushEH E P).sload 1 + 1)).sload (w + k)
      = (pushEH E P).sload (w + k) := sload_sstore_ne h1s
  rw [h1, h2, h3, h4]


/-- The `k = 0` corollary of `pushOut_sload_cached_of_config`.  The `+ 0` is discharged HERE,
where `w` is an abstract variable, rather than at a call site where it is a weld state and the
motive abstraction unfolds the whole dispatcher chain. -/
lemma pushOut_sload_cached0_of_config
    {E : EVMState} {ms : MachineState} {P q w : UInt256} {kp kk : ℕ}
    (hsepH : Clear.KeccakSlotSep.Separated (pushEH E P))
    (husedH : Clear.KeccakFresh.CacheInUsed (pushEH E P))
    (hinjH : Clear.KeccakFresh.CacheInj (pushEH E P))
    (hcw : Finmap.lookup (mkInterval ms q 64) (pushEH E P).keccak_map = some w)
    (h1s : (1 : UInt256) ≠ w)
    (hA1 : (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).2.hash_collision = false)
    (hA2 : (arrOut (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).2
        (arrOut (pushPadW E P kp).1 ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hnidx : ((pushEH E P).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (hokp : ∀ j, j < kp → PadLowOK (pushPadW E P j))
    (hok₂ : ∀ j, j < kk → StepLowOK 0 ((0 : UInt256) + 2) (pushOutW E P kp j)) :
    (pushOutW E P kp kk).1.sload w = (pushEH E P).sload w := by
  have h1s' : (1 : UInt256) ≠ w + 0 := by rw [add_zero]; exact h1s
  have h := pushOut_sload_cached_of_config (k := 0) hsepH husedH hinjH hcw
    (by decide) h1s' hA1 hA2 hnidx hokp hok₂
  rw [add_zero] at h
  exact h

/-- **DERIVED** companion to `vtiAt_wFinal_V`: the new key's `valueToIndex` entry reads back
as the old count, with no appeal to `Sep32`.

Written to touch no weld state with a normalising or backward-rewriting step.  The keccak
witness is taken at the `H3` anchor, so the whole calc runs over the abstract `wv`; the
connection to `(accOut (wF5 …) V 5).1` happens once, at the end, substituting a variable INTO
a big term rather than abstracting one out of it. -/
theorem vtiAt_wFinal_V_of_config
    {evm : EVMState} {V IX wv : UInt256} {k k2 k3 : ℕ}
    (hsepH : Clear.KeccakSlotSep.Separated (wH3 evm V IX k))
    (husedH : Clear.KeccakFresh.CacheInUsed (wH3 evm V IX k))
    (hinjH : Clear.KeccakFresh.CacheInj (wH3 evm V IX k))
    (hRwH : Clear.KeccakLowSlot.RangeInWindow (wH3 evm V IX k))
    (hCwH : Clear.KeccakLowSlot.CachedInWindow (wH3 evm V IX k))
    (hcleanV : (accOut (wF5 evm V IX k) V 5).2.hash_collision = false)
    (hcleanH3 : (wH3 evm V IX k).hash_collision = false)
    (hcleanA1 : (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2.hash_collision = false)
    (hcleanA2 : (arrOut (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).2
        (arrOut (wSP evm V IX k k2) ((0 : UInt256) + 2)).1).2.hash_collision = false)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    (haccV : (((accOut (wF5 evm V IX k) V 5).2).lookupAccount
        ((accOut (wF5 evm V IX k) V 5).2).execution_env.code_owner).isSome)
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j))
    (hcvF : Finmap.lookup (accInterval (wF5 evm V IX k) V 5)
        (wF5 evm V IX k).keccak_map = some wv)
    (hcvH : Finmap.lookup (accInterval (wH3 evm V IX k) V 5)
        (wH3 evm V IX k).keccak_map = some wv) :
    vtiAt (wFinal evm V IX k k2 k3) V = evm.sload 1 := by
  -- the pack word IS the write slot (functionality at the F5 anchor)
  have hwv : wv = (accOut (wF5 evm V IX k) V 5).1 :=
    Option.some.inj ((accOut_lookup_mono hcvF).symm.trans (accOut_caches_of_clean hcleanV))
  -- the H3-anchored keccak witness: gives `wv ≠ 1` with no rewriting at all
  have hkH := (vtiSlot_keccakV hcvH).1
  have h1V : (1 : UInt256) ≠ wv :=
    Ne.symm (Clear.KeccakLowSlot.keccak256_ne_lowSlot_of_config 1
      (Clear.KeccakLowSlot.noLowInRange_of_window (Clear.KeccakLowSlot.rangeInWindow_mstore _ _
        (Clear.KeccakLowSlot.rangeInWindow_mstore _ _ hRwH)))
      (Clear.KeccakLowSlot.noLowCached_of_window (Clear.KeccakLowSlot.cachedInWindow_mstore _ _
        (Clear.KeccakLowSlot.cachedInWindow_mstore _ _ hCwH)))
      hkH (by decide))
  -- the final-state slot pin, kept at `wv`
  have hslotF : vtiSlot (wFinal evm V IX k k2 k3) V = wv :=
    vtiSlot_pushOut (E := wS3 evm V IX k) (P := (wS2 evm V IX k).mload 64)
      (kp := k2) (kk := k3) hcvH
  show (wFinal evm V IX k k2 k3).sload (vtiSlot (wFinal evm V IX k k2 k3) V)
      = evm.sload 1
  rw [hslotF]
  calc (wFinal evm V IX k k2 k3).sload wv
      = (wH3 evm V IX k).sload wv :=
        pushOut_sload_cached0_of_config hsepH husedH hinjH hcvH h1V
          hcleanA1 hcleanA2 hnidx hokp hok₂
    _ = (wS3 evm V IX k).sload wv := sload_hashLeafOut_of_clean _ hcleanH3
    _ = evm.sload 1 := by rw [hwv]; exact sload_sstore_self haccV

/-! ### Zero-offset forms

Each is its general lemma with `k₂ = 0` discharged HERE, where every state is an abstract
variable.  At a call site the same `add_zero` would abstract over a `@[reducible]` weld state
and cost millions of heartbeats -- see the note below. -/

/-- `cached_off_ne_off` with the right-hand offset at zero. -/
lemma cached_off_ne_of_config {σ : EVMState} {I₁ I₂ : List UInt256} {r₁ r₂ k₁ : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hc₁ : Finmap.lookup I₁ σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup I₂ σ.keccak_map = some r₂)
    (hne : I₁ ≠ I₂) (hk₁ : k₁.val < Clear.KeccakInjective.lowSlotBound) :
    r₁ + k₁ ≠ r₂ := by
  have h := Clear.KeccakSlotSep.cached_off_ne_off (k₂ := (0 : UInt256)) hsep hinj hc₁ hc₂ hne hk₁ (by decide)
  rw [add_zero] at h
  exact h

/-- Cache transport through three `sstore`s, stated abstractly so no weld term is simped. -/
lemma lookup_mono_sstore3 {σ : EVMState} {a b c d e f : UInt256}
    {I : List UInt256} {w : UInt256}
    (h : Finmap.lookup I σ.keccak_map = some w) :
    Finmap.lookup I (((σ.sstore a b).sstore c d).sstore e f).keccak_map = some w := by
  simp only [keccak_map_sstoreV]
  exact h

/-- `cached_off_ne_off` with BOTH offsets at zero: two slots cached under different preimages
are different slots.  Needed where the left-hand slot is itself a weld term, so that no
`add_zero` has to be rewritten at the call site. -/
lemma cached_ne_of_config {σ : EVMState} {I₁ I₂ : List UInt256} {r₁ r₂ : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hc₁ : Finmap.lookup I₁ σ.keccak_map = some r₁)
    (hc₂ : Finmap.lookup I₂ σ.keccak_map = some r₂)
    (hne : I₁ ≠ I₂) : r₁ ≠ r₂ := by
  have h := Clear.KeccakSlotSep.cached_off_ne_off (k₁ := (0 : UInt256)) (k₂ := (0 : UInt256))
    hsep hinj hc₁ hc₂ hne (by decide) (by decide)
  rw [add_zero, add_zero] at h
  exact h

/-- `arrSlot_ne_cached64_of_clean` with the cached-side offset at zero. -/
lemma arrSlot_ne_cached64_0_of_clean
    {σ : EVMState} {ms : MachineState} {a q w j : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated (arrOut σ a).2)
    (hinj : Clear.KeccakFresh.CacheInj (arrOut σ a).2)
    (hclean : (arrOut σ a).2.hash_collision = false)
    (hcache : Finmap.lookup (mkInterval ms q 64) σ.keccak_map = some w)
    (hj : j.val < Clear.KeccakInjective.lowSlotBound) :
    (arrOut σ a).1 + j ≠ w := by
  have h := arrSlot_ne_cached64_of_clean (k := (0 : UInt256)) hsep hinj hclean hcache hj
    (by decide)
  rw [add_zero] at h
  exact h

/-- `updateWalk_sload_cached_of_config` at offset zero. -/
lemma updateWalk_sload_cached0_of_config
    (kk : ℕ) {σ : EVMState} {ms : MachineState} {ss base i idx maxN cur q w : UInt256}
    (hsep : Clear.KeccakSlotSep.Separated σ) (hused : Clear.KeccakFresh.CacheInUsed σ) (hinj : Clear.KeccakFresh.CacheInj σ)
    (hcσ : Finmap.lookup (mkInterval ms q 64) σ.keccak_map = some w)
    (hok : ∀ j, j < kk → StepLowOK ss base (updateWalk ss base j σ i idx maxN cur)) :
    ((updateWalk ss base kk σ i idx maxN cur).1).sload w = σ.sload w := by
  have h := updateWalk_sload_cached_of_config kk (k := (0 : UInt256)) hsep hused hinj hcσ
    (by decide) hok
  rw [add_zero] at h
  exact h

/-! ### Why the twin above is written the way it is

`vtiAt_wFinal_V_of_config` took four formulations.  The first three timed out at 4M
heartbeats, and none of them was a proof problem: every weld state (`wF5`, `wH3`, `wFinal`,
…) is `@[reducible]`, so any step that normalises or motive-abstracts over one unfolds the
whole dispatcher chain.  `simpa` fixing a `w + 0` cost 4M heartbeats; so did `rw [add_zero]`
on the same term; so did the statement elaboration once enough such steps accumulated.

The rule that works is not "avoid `simp`".  It is:

  * never rewrite BACKWARD over a weld state -- abstracting a big term out of a goal is the
    expensive direction, substituting a variable into one is free;
  * push every `+ 0` / `add_zero` fixup down into a lemma whose states are abstract
    variables, where it costs nothing (`pushOut_sload_cached0_of_config` exists only for
    this);
  * keep the calc running over the abstract cached word and connect to the concrete write
    slot ONCE, at the end.

Applying all three made the proof typecheck immediately. -/



/-! ### Anchors for the `vtiAt_wFinal_old` twin

The twin needs the pool triple and the `u` hit at five states along the weld chain.  Deriving
them inline exhausts the heartbeat budget -- not because any step is expensive (each group
clears at 800k on its own) but because every annotation mentions a `@[reducible]` weld state
and there are ~40 of them.  Split into two lemmas, each of which fits. -/

/-- Anchors on the retarget (`wE4`) and new-leaf (`wF4`) accessor threads. -/
lemma vtiOld_anchorsEF {evm : EVMState} {V IX x u : UInt256} {k : ℕ}
    (hsepE : Clear.KeccakSlotSep.Separated evm) (husedE : Clear.KeccakFresh.CacheInUsed evm) (hinjE : Clear.KeccakFresh.CacheInj evm)
    (hcu : Finmap.lookup (accInterval evm x 5) evm.keccak_map = some u) :
    Clear.KeccakSlotSep.Separated ((accOut (wE4 evm V IX) IX 4).2)
    ∧ Clear.KeccakFresh.CacheInj ((accOut (wE4 evm V IX) IX 4).2)
    ∧ Finmap.lookup (accInterval evm x 5)
        ((accOut (wE4 evm V IX) IX 4).2).keccak_map = some u
    ∧ Clear.KeccakSlotSep.Separated ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2)
    ∧ Clear.KeccakFresh.CacheInj ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2)
    ∧ Finmap.lookup (accInterval evm x 5)
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).keccak_map = some u := by
  have hsepG : Clear.KeccakSlotSep.Separated (guardsEvm evm V IX) := separated_guardsEvm hsepE
  have husedG : Clear.KeccakFresh.CacheInUsed (guardsEvm evm V IX) := cacheInUsed_guardsEvm husedE
  have hinjG : Clear.KeccakFresh.CacheInj (guardsEvm evm V IX) := cacheInj_guardsEvm husedE hinjE
  have hcuG : Finmap.lookup (accInterval evm x 5) (guardsEvm evm V IX).keccak_map = some u :=
    lookup_mono_guardsEvm hcu
  have hsepE4 : Clear.KeccakSlotSep.Separated (wE4 evm V IX) :=
    Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore
      (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore hsepG)))
  have husedE4 : Clear.KeccakFresh.CacheInUsed (wE4 evm V IX) :=
    Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _
      (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ husedG)))
  have hinjE4 : Clear.KeccakFresh.CacheInj (wE4 evm V IX) :=
    Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _
      (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ hinjG)))
  have hsepS2 : Clear.KeccakSlotSep.Separated (wS2 evm V IX k) := separated_insertUpdEvm k hsepG
  have husedS2 : Clear.KeccakFresh.CacheInUsed (wS2 evm V IX k) := cacheInUsed_insertUpdEvm k husedG
  have hinjS2 : Clear.KeccakFresh.CacheInj (wS2 evm V IX k) := cacheInj_insertUpdEvm k husedG hinjG
  have hcuS2 : Finmap.lookup (accInterval evm x 5) (wS2 evm V IX k).keccak_map = some u :=
    lookup_mono_insertUpdEvm k hcuG
  have hsepF4 : Clear.KeccakSlotSep.Separated (wF4 evm V IX k) :=
    Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore
      (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore hsepS2)))
  have husedF4 : Clear.KeccakFresh.CacheInUsed (wF4 evm V IX k) :=
    Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _
      (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ husedS2)))
  have hinjF4 : Clear.KeccakFresh.CacheInj (wF4 evm V IX k) :=
    Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _
      (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ hinjS2)))
  exact ⟨separated_accOut hsepE4, Clear.KeccakFresh.cacheInj_accOut husedE4 hinjE4,
    accOut_lookup_mono hcuG, separated_accOut hsepF4,
    Clear.KeccakFresh.cacheInj_accOut husedF4 hinjF4, accOut_lookup_mono hcuS2⟩

/-- Anchors on the vti write thread (`wF5`) and the two interleaved hash states. -/
lemma vtiOld_anchorsVH {evm : EVMState} {V IX x u : UInt256} {k : ℕ}
    (hsepE : Clear.KeccakSlotSep.Separated evm) (husedE : Clear.KeccakFresh.CacheInUsed evm) (hinjE : Clear.KeccakFresh.CacheInj evm)
    (hcu : Finmap.lookup (accInterval evm x 5) evm.keccak_map = some u) :
    Clear.KeccakSlotSep.Separated ((accOut (wF5 evm V IX k) V 5).2)
    ∧ Clear.KeccakFresh.CacheInj ((accOut (wF5 evm V IX k) V 5).2)
    ∧ Finmap.lookup (accInterval evm x 5)
        ((accOut (wF5 evm V IX k) V 5).2).keccak_map = some u
    ∧ Clear.KeccakSlotSep.Separated (wH3 evm V IX k) ∧ Clear.KeccakFresh.CacheInUsed (wH3 evm V IX k)
    ∧ Clear.KeccakFresh.CacheInj (wH3 evm V IX k)
    ∧ Clear.KeccakSlotSep.Separated (wH1 evm V IX) ∧ Clear.KeccakFresh.CacheInUsed (wH1 evm V IX)
    ∧ Clear.KeccakFresh.CacheInj (wH1 evm V IX)
    ∧ Finmap.lookup (accInterval evm x 5) (wH1 evm V IX).keccak_map = some u := by
  have hsepG : Clear.KeccakSlotSep.Separated (guardsEvm evm V IX) := separated_guardsEvm hsepE
  have husedG : Clear.KeccakFresh.CacheInUsed (guardsEvm evm V IX) := cacheInUsed_guardsEvm husedE
  have hinjG : Clear.KeccakFresh.CacheInj (guardsEvm evm V IX) := cacheInj_guardsEvm husedE hinjE
  have hcuG : Finmap.lookup (accInterval evm x 5) (guardsEvm evm V IX).keccak_map = some u :=
    lookup_mono_guardsEvm hcu
  have hsepS2 : Clear.KeccakSlotSep.Separated (wS2 evm V IX k) := separated_insertUpdEvm k hsepG
  have husedS2 : Clear.KeccakFresh.CacheInUsed (wS2 evm V IX k) := cacheInUsed_insertUpdEvm k husedG
  have hinjS2 : Clear.KeccakFresh.CacheInj (wS2 evm V IX k) := cacheInj_insertUpdEvm k husedG hinjG
  have hcuS2 : Finmap.lookup (accInterval evm x 5) (wS2 evm V IX k).keccak_map = some u :=
    lookup_mono_insertUpdEvm k hcuG
  have hsepFK : Clear.KeccakSlotSep.Separated ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2) :=
    separated_accOut (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore
      (Clear.StorageFrame.separated_mstore (Clear.StorageFrame.separated_mstore hsepS2))))
  have husedFK : Clear.KeccakFresh.CacheInUsed ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2) :=
    Clear.KeccakFresh.cacheInUsed_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _
      (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ husedS2))))
  have hinjFK : Clear.KeccakFresh.CacheInj ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2) :=
    Clear.KeccakFresh.cacheInj_accOut (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _
        (Clear.KeccakFresh.cacheInUsed_mstore _ _ (Clear.KeccakFresh.cacheInUsed_mstore _ _ husedS2))))
      (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _
        (Clear.KeccakFresh.cacheInj_mstore _ _ (Clear.KeccakFresh.cacheInj_mstore _ _ hinjS2))))
  have hcuFK : Finmap.lookup (accInterval evm x 5)
      ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).keccak_map = some u :=
    accOut_lookup_mono hcuS2
  have hsepF5 : Clear.KeccakSlotSep.Separated (wF5 evm V IX k) :=
    Clear.StorageFrame.separated_sstore (Clear.StorageFrame.separated_sstore (Clear.StorageFrame.separated_sstore hsepFK))
  have husedF5 : Clear.KeccakFresh.CacheInUsed (wF5 evm V IX k) :=
    Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore (Clear.StorageFrame.cacheInUsed_sstore husedFK))
  have hinjF5 : Clear.KeccakFresh.CacheInj (wF5 evm V IX k) :=
    Clear.StorageFrame.cacheInj_sstore (Clear.StorageFrame.cacheInj_sstore (Clear.StorageFrame.cacheInj_sstore hinjFK))
  exact ⟨separated_accOut hsepF5, Clear.KeccakFresh.cacheInj_accOut husedF5 hinjF5,
    accOut_lookup_mono (lookup_mono_sstore3 hcuFK),
    separated_pushEH (separated_insertNewEvm k hsepG),
    cacheInUsed_pushEH (cacheInUsed_insertNewEvm k husedG),
    cacheInj_pushEH (cacheInUsed_insertNewEvm k husedG) (cacheInj_insertNewEvm k husedG hinjG),
    separated_hashLeafOut (separated_retargetStageEvm hsepG),
    cacheInUsed_hashLeafOut (cacheInUsed_retargetStageEvm husedG),
    cacheInj_hashLeafOut (cacheInUsed_retargetStageEvm husedG)
      (cacheInj_retargetStageEvm husedG hinjG),
    lookup_mono_hashLeafOut (lookup_mono_retargetStageEvm hcuG)⟩

/-! ### `vtiAt_wFinal_old` on the derived route — NOT YET, AND THE EARLIER DIAGNOSIS WAS WRONG

Every ingredient exists and is verified: the six base-4-vs-base-5 separations are
`cached_ne_of_config` / `cached_off_ne_of_config` (both sides are cached 64-byte hits, with
`base54_interval_neV` supplying the different-preimage input), the `u` hit reaches the
`wE4`/`wF4` accessor threads through the `lookup_mono_*` family, and the frame steps have
zero-offset forms above.  A full assembly was written and every site typechecked.

It does not FIT: the proof exhausts 16M heartbeats at the tactic block, with no inner site
named.

An earlier version of this note blamed the defeq shortcuts (`hcuE4 := hcuG`,
`hcuF4 := hcuS2`), reasoning that `wS2` contains a walk recursing on a symbolic level count.
**That was measured and is false.**  Both typecheck in under 1M heartbeats, including the one
crossing `wS2`.  Bisection at 800k also clears every other anchor group individually --
`separated_insertUpdEvm`, the three-`sstore` chain to `wF5`, `separated_pushEH ∘
separated_insertNewEvm`, and the `lookup_mono` composition to `wH1`.

So no single step is pathological, which points back at plain accumulation over ~40 anchors
whose types each mention a `@[reducible]` weld state.  The inference "a 4x budget increase
changed nothing, therefore not accumulation" was too strong: 4M → 16M only rules out a total
under 16M.  A 64M attempt was inconclusive (it exceeds the practical build time here), so the
true cost is somewhere above 16M and unmeasured.

The fix to try is structural, not a bigger number: factor the anchor block into its own lemma
returning the facts it establishes, so the weld terms are elaborated once in a small context.
Do NOT do more tactic surgery on the twin -- that was six build cycles for nothing. -/


end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
