import Clear.ReasoningPrinciple

import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_insert_gate_user
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_fidelity_user

/-
  THE WELD (#67): the concrete insert closed form IS an abstract insert.

  `insertGlue_prefix` (imt_insert_gate_user) drives the L2ICT `insert`
  dispatcher arm to the concrete final state

    (pushOutW (insertNewEvm G LM NI V IX k) ((insertUpdEvm G LM NI V IX k).mload 64) k2 k3).1

  over the guards' threaded state `G = guardsEvm evm V IX`.
  `glueSeq_leafSetOf'` (imt_fidelity_user) proves the abstract set equation
  for the interleave-accurate glue chain.  This file welds them:

    `insertGlue_leafSetOf` :
      leafSetOf (concrete final evm) = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V

  with `evm` the dispatcher ENTRY state (the guard-stage keccak threads are
  bridged back by storage transparency + the entry anchor of the cache pack).

  SEGMENT MATCH (verified definitionally by the `exact` below):
  * retargetStageEvm G LM NI V IX      = glueSeq' S1 (stage + copy)      ✓
  * insertUpdEvm … k                   = walk #1 over
      leafWriteEvm (hashLeafOut S1 P1).2 0 IX (hashLeafOut S1 P1).1
    — the `hashLeaf` step `H1` and the level-0 write are the (a)-deviation,
    absorbed by `glueSeq_leafSetOf'`'s generic `H1`/`L0` segment          ✓
  * insertNewEvm … k                   = glueSeq' F4→FK→F5→S3             ✓
  * pushEH S3 P2                       = `H3` — the SECOND `hashLeaf`
    interleave (the S4-segment residual: the push hashes the struct BEFORE
    the count bump; glueSeq's original bare `S3.sstore 1 …` did not carry
    it — the primed variant does)                                          ✓
  * pushPadW / pushOutW                = count bump → padWalk →
      leafWriteEvm → updateWalk (order matches `pushInterleave_arm`)       ✓

  READ-BACK DISCHARGE (the (b)-deviation): `hkey`/`hnv` are proven, not
  assumed — `guardsEvm` materializes the window leaf by `leafReadEvm`, so
  `G.mload LM` / `G.mload (LM+64)` read back `EG.sload SLG` /
  `EG.sload (SLG+2)` (`leafRead_mload_key/nextKey`), and the pack's entry
  anchor pins `leafSlot G IX = SLG` (`guards_slot_pins`: the guards
  accessor caches `SLG` at the ENTRY interval, and Finmap-lookup
  functionality forces the pack word to agree).

  HYPOTHESES: `insertGlue_prefix`'s pointer bounds (`hpG`/`hpW`/`hpN`) and
  window guard (`hbound`), plus the fidelity packs instantiated at the
  concrete anchor states: the FIVE-anchor cache pack (entry / G / E4 / F4 /
  H3 — the guards' `leafReadEvm` bump, the two staging bumps and the two
  `hashLeaf` bumps give five junk-window regimes), cleanliness and account
  flags, decode injectivity below the count, and the walks' low-slot packs.
  The exec-driving hypotheses of `insertGlue_prefix` (caller, dedup-zero,
  value order, …) are not needed for the state-level set equation; compose
  the two theorems to speak about the dispatcher run end-to-end.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     IMTAbstract Clear.KeccakDeterminism

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.dupNamespace false

/-! ### The concrete anchor states of the insert chain -/

/-- Anchor E4 — the retarget staging state over the guards' evm (allocator
bump + three scratch writes; junk-window regime #3). -/
@[reducible] def wE4 (evm : EVMState) (V IX : UInt256) : EVMState :=
  let G := guardsEvm evm V IX
  let P := G.mload 64
  (((G.mstore 64 (P + 96)).mstore P (G.mload (guardsLM evm V IX))).mstore
      (P + 32) (evm.sload 1)).mstore (P + 64) V

/-- The retarget stage + copy state (glueSeq' `S1`). -/
@[reducible] def wS1 (evm : EVMState) (V IX : UInt256) : EVMState :=
  retargetStageEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX

/-- The first interleaved `hashLeaf` state (glueSeq' `H1`; junk regime #4). -/
@[reducible] def wH1 (evm : EVMState) (V IX : UInt256) : EVMState :=
  (hashLeafOut (wS1 evm V IX) ((guardsEvm evm V IX).mload 64)).2

/-- The post-walk-#1 state (glueSeq' `S2`). -/
@[reducible] def wS2 (evm : EVMState) (V IX : UInt256) (k : ℕ) : EVMState :=
  insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k

/-- Anchor F4 — the new-leaf staging state (junk regime #5's predecessor). -/
@[reducible] def wF4 (evm : EVMState) (V IX : UInt256) (k : ℕ) : EVMState :=
  let S2 := wS2 evm V IX k
  let P2 := S2.mload 64
  (((S2.mstore 64 (P2 + 96)).mstore P2 V).mstore
      (P2 + 32) ((guardsEvm evm V IX).mload (guardsLM evm V IX + 32))).mstore
      (P2 + 64) ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64))

/-- The new-leaf copy state (glueSeq' `F5`). -/
@[reducible] def wF5 (evm : EVMState) (V IX : UInt256) (k : ℕ) : EVMState :=
  let P2 := (wS2 evm V IX k).mload 64
  let FK := (accOut (wF4 evm V IX k) (evm.sload 1) 4).2
  let SL2 := (accOut (wF4 evm V IX k) (evm.sload 1) 4).1
  ((FK.sstore SL2 (FK.mload P2)).sstore
      (SL2 + 1) (FK.mload (P2 + 32))).sstore (SL2 + 2) (FK.mload (P2 + 64))

/-- The post-vti-registration state (glueSeq' `S3`). -/
@[reducible] def wS3 (evm : EVMState) (V IX : UInt256) (k : ℕ) : EVMState :=
  insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k

/-- Anchor H3 — the second interleaved `hashLeaf` state (`pushEH`; junk
regime #5). -/
@[reducible] def wH3 (evm : EVMState) (V IX : UInt256) (k : ℕ) : EVMState :=
  pushEH (wS3 evm V IX k) ((wS2 evm V IX k).mload 64)

/-- The post-padding state (glueSeq' `SP`). -/
@[reducible] def wSP (evm : EVMState) (V IX : UInt256) (k k2 : ℕ) : EVMState :=
  (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2).1

/-- The concrete final evm of `insertGlue_prefix` (verbatim). -/
@[reducible] def wFinal (evm : EVMState) (V IX : UInt256) (k k2 k3 : ℕ) : EVMState :=
  (pushOutW (insertNewEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k)
      ((insertUpdEvm (guardsEvm evm V IX) (guardsLM evm V IX) (evm.sload 1) V IX k).mload 64)
      k2 k3).1

/-! ### `hashLeafOut` storage transparency -/

/-- **The `hashLeaf` step never `sstore`s**: its five scratch/allocator
`mstore`s and the keccak call leave storage untouched (clean branch). -/
lemma sload_hashLeafOut_of_clean {σ : EVMState} {leaf : UInt256} (t : UInt256)
    (h : (hashLeafOut σ leaf).2.hash_collision = false) :
    (hashLeafOut σ leaf).2.sload t = σ.sload t := by
  unfold hashLeafOut at h ⊢
  rw [sload_keccakOut_of_clean t h]
  rfl

/-! ### The guard-stage read-backs (deviation (b)) -/

/-- The struct materialization reads the `value` field back: `mload` at the
struct base returns the copied `sload` (two disjoint later writes skipped,
then the base write itself). -/
lemma leafRead_mload_key {σ : EVMState} {slot : UInt256}
    (hp : (σ.mload 64).val + 96 ≤ 18446744073709551615) :
    (leafReadEvm σ slot).mload (σ.mload 64) = σ.sload slot := by
  have hsz : UInt256.size = 2 ^ 256 := by norm_num
  set P := σ.mload 64
  have hv32 : (P + 32).val = P.val + 32 := by
    show (P.val + ((32 : UInt256)).val) % UInt256.size = P.val + 32
    have h32 : ((32 : UInt256)).val = 32 := rfl
    rw [h32]
    exact Nat.mod_eq_of_lt (by omega)
  have hv64 : (P + 64).val = P.val + 64 := by
    show (P.val + ((64 : UInt256)).val) % UInt256.size = P.val + 64
    have h64 : ((64 : UInt256)).val = 64 := rfl
    rw [h64]
    exact Nat.mod_eq_of_lt (by omega)
  show ((((σ.mstore 64 (P + 96)).mstore P (σ.sload slot)).mstore
      (P + 32) (σ.sload (slot + 1))).mstore
      (P + 64) (σ.sload (slot + 2))).mload P = σ.sload slot
  rw [mload_mstore_outside _ (P + 64) (σ.sload (slot + 2)) P
      (by rw [hv64]; omega) (by omega) (Or.inl (by rw [hv64]; omega))]
  rw [mload_mstore_outside _ (P + 32) (σ.sload (slot + 1)) P
      (by rw [hv32]; omega) (by omega) (Or.inl (by rw [hv32]))]
  exact mload_mstore_self_at _ _ _ (by omega)

/-- The struct materialization reads the `nextValue` field back (`+64` is
the last write). -/
lemma leafRead_mload_nextKey {σ : EVMState} {slot : UInt256}
    (hp : (σ.mload 64).val + 96 ≤ 18446744073709551615) :
    (leafReadEvm σ slot).mload (σ.mload 64 + 64) = σ.sload (slot + 2) := by
  have hsz : UInt256.size = 2 ^ 256 := by norm_num
  set P := σ.mload 64
  have hv64 : (P + 64).val = P.val + 64 := by
    show (P.val + ((64 : UInt256)).val) % UInt256.size = P.val + 64
    have h64 : ((64 : UInt256)).val = 64 := rfl
    rw [h64]
    exact Nat.mod_eq_of_lt (by omega)
  show ((((σ.mstore 64 (P + 96)).mstore P (σ.sload slot)).mstore
      (P + 32) (σ.sload (slot + 1))).mstore
      (P + 64) (σ.sload (slot + 2))).mload (P + 64) = σ.sload (slot + 2)
  exact mload_mstore_self_at _ _ _ (by rw [hv64]; omega)

/-- **The guards' evm is storage-transparent**: `guardsEvm` is two clean
accessor keccak steps plus memory writes. -/
lemma guards_sload {evm : EVMState} {V IX : UInt256}
    (hcleanEG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    (t : UInt256) :
    (guardsEvm evm V IX).sload t = evm.sload t := by
  have hcleanPre : ((accOut evm V 5).2).hash_collision = false :=
    accOut_clean_backward hcleanEG
  have h1 : (guardsEvm evm V IX).sload t
      = ((accOut (accOut evm V 5).2 IX 4).2).sload t := rfl
  rw [h1, sload_accOut_of_clean t hcleanEG, sload_accOut_of_clean t hcleanPre]

/-- **The pack word at index `IX` IS the guards' computed slot**: the guards
accessor caches its output `SLG` at the ENTRY-anchored preimage interval
(its scratch states agree with `evm` on the junk window), and any
entry-anchored cached word for `IX` — transported into the same map — must
agree by lookup functionality.  This is the coherence that discharges the
`hkey`/`hnv` read-backs. -/
lemma guards_slot_pins {evm : EVMState} {V IX wIX : UInt256}
    (hcleanEG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    (h0 : Finmap.lookup (accInterval evm IX 4) evm.keccak_map = some wIX) :
    wIX = (accOut (accOut evm V 5).2 IX 4).1 := by
  have hIntPre : accInterval (accOut evm V 5).2 IX 4 = accInterval evm IX 4 :=
    accInterval_eq (fun b hb1 _ => accOut_junk_window hb1)
  have hSLGc : Finmap.lookup (accInterval evm IX 4)
      ((accOut (accOut evm V 5).2 IX 4).2).keccak_map
      = some ((accOut (accOut evm V 5).2 IX 4).1) := by
    rw [← hIntPre]
    exact accOut_caches_of_clean hcleanEG
  have hwtrans : Finmap.lookup (accInterval evm IX 4)
      ((accOut (accOut evm V 5).2 IX 4).2).keccak_map = some wIX :=
    accOut_lookup_mono (accOut_lookup_mono h0)
  exact Option.some.inj (hwtrans.symm.trans hSLGc)

/-! ### THE WELD -/

open Clear.KeccakDeterminism in
/-- **THE INSERT-FIDELITY WELD (#67)** — the concrete final state of
`insertGlue_prefix` satisfies the abstract insert equation at the
dispatcher ENTRY state:

`leafSetOf (final) = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V`.

Composed with `insertGlue_prefix` (which produces exactly
`wFinal evm V IX k k2 k3` as the dispatcher's post-state) and
`leafSetOf_evolution_step` (#62's capstone packaging), the deployed insert
IS an `IMTAbstract.Evolution` step's set effect.  See the file header for
the hypothesis inventory and the segment-match audit. -/
theorem insertGlue_leafSetOf
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    -- window guard + count arithmetic (entry state)
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    -- guards-stage accessor cleanliness (vti read + leaves read)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    -- allocator bounds (hpG/hpW/hpN as in `insertGlue_prefix`, plus floors)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowW : 96 ≤ ((guardsEvm evm V IX).mload 64).val)
    (hpN : ((wS2 evm V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowN : 96 ≤ ((wS2 evm V IX k).mload 64).val)
    -- cleanliness of the write-stage keccak steps
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
    -- account presence where `sstore` must not be a no-op
    (haccEK : (((accOut (wE4 evm V IX) IX 4).2).lookupAccount
        ((accOut (wE4 evm V IX) IX 4).2).execution_env.code_owner).isSome)
    (haccFK : (((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).lookupAccount
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).execution_env.code_owner).isSome)
    (haccH3 : ((wH3 evm V IX k).lookupAccount
        (wH3 evm V IX k).execution_env.code_owner).isSome)
    -- the level-0 element indices are small
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    -- THE FIVE-ANCHOR CACHE PACK (entry / guards / E4 / F4 / H3)
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
    -- decode injectivity below the count, at the entry state
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    -- the walks' low-slot packs (concrete walk states)
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j)) :
    leafSetOf (wFinal evm V IX k k2 k3)
      = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
  have hwlt : IX.val < (evm.sload 1).val := hbound
  -- ===== the guards-stage bridge: G agrees with the entry state =====
  have hdecGm : ∀ m : ℕ, m ≤ (evm.sload 1).val →
      decodeLeaf (guardsEvm evm V IX) (m : UInt256) = decodeLeaf evm (m : UInt256) := by
    intro m hm
    obtain ⟨wm, h0, hG, _, _, _⟩ := hcach m hm
    unfold decodeLeaf
    rw [(leafSlot_keccak hG).2, (leafSlot_keccak h0).2,
        guards_sload hcleanG wm, guards_sload hcleanG (wm + 2)]
  have hsetG : leafSetOf (guardsEvm evm V IX) = leafSetOf evm := by
    unfold leafSetOf
    rw [guards_sload hcleanG 1]
    refine Finset.image_congr ?_
    intro x hx
    rw [Finset.mem_coe, Finset.mem_range] at hx
    exact hdecGm x (le_of_lt hx)
  have hdIX : decodeLeaf (guardsEvm evm V IX) IX = decodeLeaf evm IX := by
    have h := hdecGm IX.val (le_of_lt hwlt)
    rwa [Fin.cast_val_eq_self IX] at h
  -- ===== the read-backs (deviation (b), discharged) =====
  have hkeyG : (guardsEvm evm V IX).mload (guardsLM evm V IX)
      = (decodeLeaf (guardsEvm evm V IX) IX).key := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1) :=
      leafRead_mload_key hpG
    have hdk : (decodeLeaf (guardsEvm evm V IX) IX).key
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX) := rfl
    rw [hr, hdk, hslotG]
    rfl
  have hnvG : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
      = (decodeLeaf (guardsEvm evm V IX) IX).nextKey := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1 + 2) :=
      leafRead_mload_nextKey hpG
    have hdn : (decodeLeaf (guardsEvm evm V IX) IX).nextKey
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX + 2) := rfl
    rw [hr, hdn, hslotG]
    rfl
  -- ===== instantiate the interleave-accurate glue-sequence theorem =====
  have hmain := glueSeq_leafSetOf'
    (evm := guardsEvm evm V IX)
    (H1 := wH1 evm V IX)
    (H3 := wH3 evm V IX k)
    (LM := guardsLM evm V IX) (NI := evm.sload 1) (V := V) (IX := IX)
    (NI4 := (guardsEvm evm V IX).mload (guardsLM evm V IX + 32))
    (NV5 := (guardsEvm evm V IX).mload (guardsLM evm V IX + 64))
    (ss₀ := 0) (idx₀ := IX)
    (hl₀ := (hashLeafOut (wS1 evm V IX) ((guardsEvm evm V IX).mload 64)).1)
    (ss₁ := 0) (base₁ := 2) (i₁ := 0) (idx₁ := IX)
    (maxN₁ := (wH1 evm V IX).sload 1 - 1)
    (cur₁ := (hashLeafOut (wS1 evm V IX) ((guardsEvm evm V IX).mload 64)).1)
    (kk₁ := k)
    (ip := 0) (om := (wH3 evm V IX k).sload 1 - 1) (mp := (wH3 evm V IX k).sload 1)
    (kp := k2)
    (ssw := 0) (nidx := (wH3 evm V IX k).sload 1)
    (hl := pushHL (wS3 evm V IX k) ((wS2 evm V IX k).mload 64))
    (ss₂ := 0) (base₂ := (0 : UInt256) + 2) (i₂ := 0)
    (idx₂ := (wH3 evm V IX k).sload 1)
    (maxN₂ := (wSP evm V IX k k2).sload ((0 : UInt256) + 1) - 1)
    (cur₂ := pushHL (wS3 evm V IX k) ((wS2 evm V IX k).mload 64))
    (kk₂ := k3)
    -- window guard + count arithmetic, transported to G
    (by rw [guards_sload hcleanG 1]; exact hbound)
    (by rw [guards_sload hcleanG 1]; exact hnw)
    ((guards_sload hcleanG 1).symm)
    -- read-backs
    hkeyG
    hnvG
    -- interleaved-hash storage transparency
    (fun t => sload_hashLeafOut_of_clean t hcleanH1)
    (fun t => sload_hashLeafOut_of_clean t hcleanH3)
    -- allocator bounds
    hplowW
    (by omega)
    hplowN
    (show ((wS2 evm V IX k).mload 64).val + 128 ≤ 2 ^ 256 by omega)
    -- cleanliness
    hclean4 hcleanF hcleanV hcleanB1 hcleanB2 hcleanA1 hcleanA2
    -- account presence
    haccEK haccFK haccH3
    -- small element indices
    hIXlow hnidx
    -- the quad-anchor pack (drop the entry anchor)
    (by
      intro m hm
      rw [guards_sload hcleanG 1] at hm
      obtain ⟨wm, _, h2, h3, h4, h5⟩ := hcach m hm
      exact ⟨wm, h2, h3, h4, h5⟩)
    -- decode injectivity, transported to G
    (by
      intro m hm m' hm' heq
      rw [guards_sload hcleanG 1] at hm hm'
      refine hinj m hm m' hm' ?_
      rw [← hdecGm m (le_of_lt hm), ← hdecGm m' (le_of_lt hm')]
      exact heq)
    -- low-slot packs
    hok₁ hokp hok₂
  -- ===== weld: the concrete final state IS the glueSeq' chain =====
  calc leafSetOf (wFinal evm V IX k k2 k3)
      = imtInsert (leafSetOf (guardsEvm evm V IX))
          (decodeLeaf (guardsEvm evm V IX) IX) V := hmain
    _ = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
        rw [hsetG, hdIX]

/-! ### THE EVOLUTION PACKAGING (#68)

The remaining stitch from the weld to `IMTAbstract.Evolution`: the window
facts.  Ground truth (`yul/L2InteropCommitmentTree.yul` 199/218-227/177):

* the value-order gate `if iszero(lt(_2, value0)) revert` passes iff
  `lowLeaf.value < _value` — the STRICT lower edge (`valueOrder_pass`'s
  `hlt`), and `_2` is the guards' `mload` of the materialized low-leaf
  struct, i.e. `(decodeLeaf evm IX).key` by the read-back discharge;
* the search loop breaks iff `¬(nextValue ≠ 0 ∧ nextValue < _value)`,
  i.e. `nextValue = 0 ∨ _value ≤ nextValue` — the WEAK upper edge
  (`searchLoop_zero`'s `hwin`; `nextValue = 0` is the last-leaf sentinel);
* the dedup gate requires `valueToIndex[_value] = 0`
  (`insert_dedup_pass`'s `hz`) — the freshness of `V`.

The weak upper edge upgrades to the strict window `Evolution` demands via
`window_strict_of_not_mem`, which consumes the ABSTRACT freshness
`V ∉ keys (leafSetOf evm)` and the no-dangling-links invariant
`NextClosed (leafSetOf evm)`.  Both are taken as named hypotheses here:

* `hclosed` is the list well-formedness that `evolution_sound` maintains
  along any history from a sound genesis — at the composition site it is
  free, not an extra trust assumption;
* `hfresh` is the semantic content of the dedup gate: the concrete pin is
  `valueToIndex[V] = 0` (`hz` of `insertGlue_prefix`), and identifying
  that storage fact with `V ∉ keys (leafSetOf evm)` needs the
  vti-coherence storage invariant ("every decoded key has a nonzero
  `valueToIndex` entry"), which the corpus does not yet establish — it is
  NOT fabricated here.
-/

/-- **Pure step packaging**: a pinned insert fact between two snapshots is
the literal insert disjunct of `IMTAbstract.Evolution` at any history
position with matching snapshots — exactly the step obligation
`Evolution S` demands at `n`. -/
theorem evolution_disjunct_of_step {A B : Finset AbsLeaf} {W₀ : AbsLeaf}
    {v : UInt256}
    (hmem : W₀ ∈ A) (hlow : W₀.key < v)
    (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey)
    (heq : B = imtInsert A W₀ v)
    {S : ℕ → Finset AbsLeaf} {n : ℕ}
    (hSn : S n = A) (hSn1 : S (n+1) = B) :
    S (n+1) = S n
      ∨ ∃ W₀ v, W₀ ∈ S n ∧ W₀.key < v ∧ (W₀.nextKey = 0 ∨ v < W₀.nextKey)
          ∧ S (n+1) = imtInsert (S n) W₀ v := by
  refine Or.inr ⟨W₀, v, ?_, hlow, hwin, ?_⟩
  · rw [hSn]; exact hmem
  · rw [hSn1, hSn]; exact heq

open Clear.KeccakDeterminism in
/-- **THE EVOLUTION PACKAGING (#68)** — under the weld's hypothesis
surface plus what the guard closed forms pin (`hvo` = `valueOrder_pass`,
`hwin` = `searchLoop_zero`'s break condition — both verbatim the
`insertGlue_prefix` hypotheses of the same names) and the two abstract
list facts (`hclosed`/`hfresh`, see the section header), the dispatcher
post-state is a WITNESSED abstract insert step:

* the window leaf `decodeLeaf evm IX` is a member of the current set,
* the window is STRICT on both sides
  (`key < V` and `nextKey = 0 ∨ V < nextKey`),
* the new set is `imtInsert` of the old — i.e. the insert disjunct of
  `IMTAbstract.Evolution`, with the witnesses pinned.

`evolution_disjunct_of_step` turns this into the literal `Evolution` step
obligation at any history position; through `evolution_invariant`,
`delivered_and_reclaimed_impossible` (#34) and
`delivered_leg_available_forever` (#60), the deployed insert now carries
the cross-chain atomicity story. -/
theorem insertGlue_evolution
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    -- window guard + count arithmetic (entry state)
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    -- WHAT THE GUARDS PIN: the value-order gate (strict lower edge) and
    -- the search loop's break (weak upper edge) — `insertGlue_prefix`'s
    -- `hvo`/`hwin`, definitionally (guardsEvm/guardsLM are reducible)
    (hvo : (guardsEvm evm V IX).mload (guardsLM evm V IX) < V)
    (hwin : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64) = 0
        ∨ ¬ ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64) < V))
    -- the abstract list invariants (see the section header)
    (hclosed : NextClosed (leafSetOf evm))
    (hfresh : V ∉ IMTAbstract.keys (leafSetOf evm))
    -- guards-stage accessor cleanliness (vti read + leaves read)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    -- allocator bounds (hpG/hpW/hpN as in `insertGlue_prefix`, plus floors)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowW : 96 ≤ ((guardsEvm evm V IX).mload 64).val)
    (hpN : ((wS2 evm V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowN : 96 ≤ ((wS2 evm V IX k).mload 64).val)
    -- cleanliness of the write-stage keccak steps
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
    -- account presence where `sstore` must not be a no-op
    (haccEK : (((accOut (wE4 evm V IX) IX 4).2).lookupAccount
        ((accOut (wE4 evm V IX) IX 4).2).execution_env.code_owner).isSome)
    (haccFK : (((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).lookupAccount
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).execution_env.code_owner).isSome)
    (haccH3 : ((wH3 evm V IX k).lookupAccount
        (wH3 evm V IX k).execution_env.code_owner).isSome)
    -- the level-0 element indices are small
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    -- THE FIVE-ANCHOR CACHE PACK (entry / guards / E4 / F4 / H3)
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
    -- decode injectivity below the count, at the entry state
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    -- the walks' low-slot packs (concrete walk states)
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j)) :
    decodeLeaf evm IX ∈ leafSetOf evm
    ∧ (decodeLeaf evm IX).key < V
    ∧ ((decodeLeaf evm IX).nextKey = 0 ∨ V < (decodeLeaf evm IX).nextKey)
    ∧ leafSetOf (wFinal evm V IX k k2 k3)
        = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
  have hwlt : IX.val < (evm.sload 1).val := hbound
  -- ===== MEMBERSHIP: the window leaf is in the abstract set =====
  have hmem : decodeLeaf evm IX ∈ leafSetOf evm := by
    unfold leafSetOf
    exact Finset.mem_image.mpr
      ⟨IX.val, Finset.mem_range.mpr hwlt, by rw [Fin.cast_val_eq_self]⟩
  -- ===== the guards-stage read-backs (as in the weld) =====
  have hdIX : decodeLeaf (guardsEvm evm V IX) IX = decodeLeaf evm IX := by
    obtain ⟨wm, h0, hG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at h0 hG
    unfold decodeLeaf
    rw [(leafSlot_keccak hG).2, (leafSlot_keccak h0).2,
        guards_sload hcleanG wm, guards_sload hcleanG (wm + 2)]
  have hkeyG : (guardsEvm evm V IX).mload (guardsLM evm V IX)
      = (decodeLeaf (guardsEvm evm V IX) IX).key := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1) :=
      leafRead_mload_key hpG
    have hdk : (decodeLeaf (guardsEvm evm V IX) IX).key
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX) := rfl
    rw [hr, hdk, hslotG]
    rfl
  have hnvG : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
      = (decodeLeaf (guardsEvm evm V IX) IX).nextKey := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1 + 2) :=
      leafRead_mload_nextKey hpG
    have hdn : (decodeLeaf (guardsEvm evm V IX) IX).nextKey
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX + 2) := rfl
    rw [hr, hdn, hslotG]
    rfl
  -- ===== WINDOW FACT 1: the strict lower edge (value-order gate) =====
  have hlow : (decodeLeaf evm IX).key < V := by
    rw [← hdIX, ← hkeyG]
    exact hvo
  -- ===== WINDOW FACT 2: the weak upper edge (search-loop break) =====
  have hweak : (decodeLeaf evm IX).nextKey = 0
      ∨ V ≤ (decodeLeaf evm IX).nextKey := by
    rw [← hdIX, ← hnvG]
    rcases hwin with h0 | hge
    · exact Or.inl h0
    · exact Or.inr (not_lt.mp hge)
  -- ===== STRICTNESS UPGRADE: freshness excludes `V = nextKey` =====
  have hstrict : (decodeLeaf evm IX).nextKey = 0
      ∨ V < (decodeLeaf evm IX).nextKey :=
    window_strict_of_not_mem hclosed hmem hfresh hweak
  -- ===== PACKAGE with the weld's set equation =====
  exact ⟨hmem, hlow, hstrict,
    insertGlue_leafSetOf hbound hnw hcleanG hpG hpW hplowW hpN hplowN
      hclean4 hcleanF hcleanV hcleanH1 hcleanH3 hcleanB1 hcleanB2 hcleanA1
      hcleanA2 haccEK haccFK haccH3 hIXlow hnidx hcach hinj hok₁ hokp hok₂⟩

open Clear.KeccakDeterminism in
/-- **The Evolution insert disjunct, verbatim** — `insertGlue_evolution`
existentially packaged in exactly the shape `leafSetOf_evolution_step`
produces (and `IMTAbstract.Evolution`'s insert disjunct consumes, via
`evolution_disjunct_of_step`): some window leaf in the current abstract
set, a fresh key through its strict window, and the dispatcher post-state
equal to the `imtInsert`. -/
theorem insertGlue_evolution_step
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    (hvo : (guardsEvm evm V IX).mload (guardsLM evm V IX) < V)
    (hwin : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64) = 0
        ∨ ¬ ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64) < V))
    (hclosed : NextClosed (leafSetOf evm))
    (hfresh : V ∉ IMTAbstract.keys (leafSetOf evm))
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
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j)) :
    ∃ W₀ v', W₀ ∈ leafSetOf evm ∧ W₀.key < v'
      ∧ (W₀.nextKey = 0 ∨ v' < W₀.nextKey)
      ∧ leafSetOf (wFinal evm V IX k k2 k3)
          = imtInsert (leafSetOf evm) W₀ v' := by
  obtain ⟨hmem, hlow, hstrict, hset⟩ := insertGlue_evolution hbound hnw hvo hwin
    hclosed hfresh hcleanG hpG hpW hplowW hpN hplowN hclean4 hcleanF hcleanV
    hcleanH1 hcleanH3 hcleanB1 hcleanB2 hcleanA1 hcleanA2 haccEK haccFK haccH3
    hIXlow hnidx hcach hinj hok₁ hokp hok₂
  exact ⟨decodeLeaf evm IX, V, hmem, hlow, hstrict, hset⟩


set_option maxHeartbeats 1600000 in
/-- **THE INSERT-FIDELITY WELD, AXIOM-FREE.**  `insertGlue_leafSetOf`'s only axiom source is
its `glueSeq_leafSetOf'` call, so this is a forwarding job -- but it forwards to a twin whose
hypotheses live at three different states along the weld chain.  The transport lemmas in
`imt_insert_gate` collapse that: all fifteen derive from the five pool/window facts at the
dispatcher ENTRY state.

The cache pack gains two entries, the E4-anchored accessor interval cached at `wH1` and at
`wH3`.  The walk frames pin their slots at `wE4`, so a hit at a walk's own interval is the
wrong preimage list; the pack has to say the value agrees. -/
theorem insertGlue_leafSetOf_of_config
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    -- the five pool/window facts, at the ENTRY state only
    (hsepE : Clear.KeccakSlotSep.Separated evm)
    (husedE : Clear.KeccakFresh.CacheInUsed evm)
    (hinjE : Clear.KeccakFresh.CacheInj evm)
    (hRwE : Clear.KeccakLowSlot.RangeInWindow evm)
    (hCwE : Clear.KeccakLowSlot.CachedInWindow evm)
    -- window guard + count arithmetic (entry state)
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    -- guards-stage accessor cleanliness (vti read + leaves read)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    -- allocator bounds (hpG/hpW/hpN as in `insertGlue_prefix`, plus floors)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowW : 96 ≤ ((guardsEvm evm V IX).mload 64).val)
    (hpN : ((wS2 evm V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowN : 96 ≤ ((wS2 evm V IX k).mload 64).val)
    -- cleanliness of the write-stage keccak steps
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
    -- account presence where `sstore` must not be a no-op
    (haccEK : (((accOut (wE4 evm V IX) IX 4).2).lookupAccount
        ((accOut (wE4 evm V IX) IX 4).2).execution_env.code_owner).isSome)
    (haccFK : (((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).lookupAccount
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).execution_env.code_owner).isSome)
    (haccH3 : ((wH3 evm V IX k).lookupAccount
        (wH3 evm V IX k).execution_env.code_owner).isSome)
    -- the level-0 element indices are small
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    -- THE FIVE-ANCHOR CACHE PACK (entry / guards / E4 / F4 / H3)
    (hcach : ∀ m : ℕ, m ≤ (evm.sload 1).val → ∃ wm,
      Finmap.lookup (accInterval evm (m : UInt256) 4) evm.keccak_map = some wm
      ∧ Finmap.lookup (accInterval (guardsEvm evm V IX) (m : UInt256) 4)
          (guardsEvm evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wE4 evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wF4 evm V IX k) (m : UInt256) 4)
          (wF4 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wH1 evm V IX).keccak_map = some wm)
    -- decode injectivity below the count, at the entry state
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    -- the walks' low-slot packs (concrete walk states)
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j)) :
    leafSetOf (wFinal evm V IX k k2 k3)
      = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
  have hwlt : IX.val < (evm.sload 1).val := hbound
  -- ===== the guards-stage bridge: G agrees with the entry state =====
  have hdecGm : ∀ m : ℕ, m ≤ (evm.sload 1).val →
      decodeLeaf (guardsEvm evm V IX) (m : UInt256) = decodeLeaf evm (m : UInt256) := by
    intro m hm
    obtain ⟨wm, h0, hG, _, _, _, _, _⟩ := hcach m hm
    unfold decodeLeaf
    rw [(leafSlot_keccak hG).2, (leafSlot_keccak h0).2,
        guards_sload hcleanG wm, guards_sload hcleanG (wm + 2)]
  have hsetG : leafSetOf (guardsEvm evm V IX) = leafSetOf evm := by
    unfold leafSetOf
    rw [guards_sload hcleanG 1]
    refine Finset.image_congr ?_
    intro x hx
    rw [Finset.mem_coe, Finset.mem_range] at hx
    exact hdecGm x (le_of_lt hx)
  have hdIX : decodeLeaf (guardsEvm evm V IX) IX = decodeLeaf evm IX := by
    have h := hdecGm IX.val (le_of_lt hwlt)
    rwa [Fin.cast_val_eq_self IX] at h
  -- ===== the read-backs (deviation (b), discharged) =====
  have hkeyG : (guardsEvm evm V IX).mload (guardsLM evm V IX)
      = (decodeLeaf (guardsEvm evm V IX) IX).key := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1) :=
      leafRead_mload_key hpG
    have hdk : (decodeLeaf (guardsEvm evm V IX) IX).key
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX) := rfl
    rw [hr, hdk, hslotG]
    rfl
  have hnvG : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
      = (decodeLeaf (guardsEvm evm V IX) IX).nextKey := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1 + 2) :=
      leafRead_mload_nextKey hpG
    have hdn : (decodeLeaf (guardsEvm evm V IX) IX).nextKey
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX + 2) := rfl
    rw [hr, hdn, hslotG]
    rfl
  -- ===== instantiate the interleave-accurate glue-sequence theorem =====
  -- the five facts at the three glueSeq entry states, all derived from `evm`
  have hsepG : Clear.KeccakSlotSep.Separated (guardsEvm evm V IX) := separated_guardsEvm hsepE
  have husedG : Clear.KeccakFresh.CacheInUsed (guardsEvm evm V IX) := cacheInUsed_guardsEvm husedE
  have hinjG : Clear.KeccakFresh.CacheInj (guardsEvm evm V IX) := cacheInj_guardsEvm husedE hinjE
  have hRwG : Clear.KeccakLowSlot.RangeInWindow (guardsEvm evm V IX) := rangeInWindow_guardsEvm hRwE
  have hCwG : Clear.KeccakLowSlot.CachedInWindow (guardsEvm evm V IX) :=
    cachedInWindow_guardsEvm hRwE hCwE
  have hsepS1 : Clear.KeccakSlotSep.Separated (wS1 evm V IX) := separated_retargetStageEvm hsepG
  have husedS1 : Clear.KeccakFresh.CacheInUsed (wS1 evm V IX) := cacheInUsed_retargetStageEvm husedG
  have hinjS1 : Clear.KeccakFresh.CacheInj (wS1 evm V IX) := cacheInj_retargetStageEvm husedG hinjG
  have hRwS1 : Clear.KeccakLowSlot.RangeInWindow (wS1 evm V IX) := rangeInWindow_retargetStageEvm hRwG
  have hCwS1 : Clear.KeccakLowSlot.CachedInWindow (wS1 evm V IX) :=
    cachedInWindow_retargetStageEvm hRwG hCwG
  have hsepH1 : Clear.KeccakSlotSep.Separated (wH1 evm V IX) := separated_hashLeafOut hsepS1
  have husedH1 : Clear.KeccakFresh.CacheInUsed (wH1 evm V IX) := cacheInUsed_hashLeafOut husedS1
  have hinjH1 : Clear.KeccakFresh.CacheInj (wH1 evm V IX) := cacheInj_hashLeafOut husedS1 hinjS1
  have hRwH1 : Clear.KeccakLowSlot.RangeInWindow (wH1 evm V IX) := rangeInWindow_hashLeafOut hRwS1
  have hCwH1 : Clear.KeccakLowSlot.CachedInWindow (wH1 evm V IX) := cachedInWindow_hashLeafOut hRwS1 hCwS1
  have hsepS3 : Clear.KeccakSlotSep.Separated (wS3 evm V IX k) := separated_insertNewEvm k hsepG
  have husedS3 : Clear.KeccakFresh.CacheInUsed (wS3 evm V IX k) := cacheInUsed_insertNewEvm k husedG
  have hinjS3 : Clear.KeccakFresh.CacheInj (wS3 evm V IX k) := cacheInj_insertNewEvm k husedG hinjG
  have hRwS3 : Clear.KeccakLowSlot.RangeInWindow (wS3 evm V IX k) := rangeInWindow_insertNewEvm k hRwG
  have hCwS3 : Clear.KeccakLowSlot.CachedInWindow (wS3 evm V IX k) :=
    cachedInWindow_insertNewEvm k hRwG hCwG
  have hsepH3 : Clear.KeccakSlotSep.Separated (wH3 evm V IX k) := separated_pushEH hsepS3
  have husedH3 : Clear.KeccakFresh.CacheInUsed (wH3 evm V IX k) := cacheInUsed_pushEH husedS3
  have hinjH3 : Clear.KeccakFresh.CacheInj (wH3 evm V IX k) := cacheInj_pushEH husedS3 hinjS3
  have hRwH3 : Clear.KeccakLowSlot.RangeInWindow (wH3 evm V IX k) := rangeInWindow_pushEH hRwS3
  have hCwH3 : Clear.KeccakLowSlot.CachedInWindow (wH3 evm V IX k) := cachedInWindow_pushEH hRwS3 hCwS3
  have hmain := glueSeq_leafSetOf'_of_config
    hsepG husedG hinjG hRwG hCwG
    hsepH1 husedH1 hinjH1 hRwH1 hCwH1 hRwH3 hCwH3
    hsepH3 husedH3 hinjH3
    (evm := guardsEvm evm V IX)
    (H1 := wH1 evm V IX)
    (H3 := wH3 evm V IX k)
    (LM := guardsLM evm V IX) (NI := evm.sload 1) (V := V) (IX := IX)
    (NI4 := (guardsEvm evm V IX).mload (guardsLM evm V IX + 32))
    (NV5 := (guardsEvm evm V IX).mload (guardsLM evm V IX + 64))
    (ss₀ := 0) (idx₀ := IX)
    (hl₀ := (hashLeafOut (wS1 evm V IX) ((guardsEvm evm V IX).mload 64)).1)
    (ss₁ := 0) (base₁ := 2) (i₁ := 0) (idx₁ := IX)
    (maxN₁ := (wH1 evm V IX).sload 1 - 1)
    (cur₁ := (hashLeafOut (wS1 evm V IX) ((guardsEvm evm V IX).mload 64)).1)
    (kk₁ := k)
    (ip := 0) (om := (wH3 evm V IX k).sload 1 - 1) (mp := (wH3 evm V IX k).sload 1)
    (kp := k2)
    (ssw := 0) (nidx := (wH3 evm V IX k).sload 1)
    (hl := pushHL (wS3 evm V IX k) ((wS2 evm V IX k).mload 64))
    (ss₂ := 0) (base₂ := (0 : UInt256) + 2) (i₂ := 0)
    (idx₂ := (wH3 evm V IX k).sload 1)
    (maxN₂ := (wSP evm V IX k k2).sload ((0 : UInt256) + 1) - 1)
    (cur₂ := pushHL (wS3 evm V IX k) ((wS2 evm V IX k).mload 64))
    (kk₂ := k3)
    -- window guard + count arithmetic, transported to G
    (by rw [guards_sload hcleanG 1]; exact hbound)
    (by rw [guards_sload hcleanG 1]; exact hnw)
    ((guards_sload hcleanG 1).symm)
    -- read-backs
    hkeyG
    hnvG
    -- interleaved-hash storage transparency
    (fun t => sload_hashLeafOut_of_clean t hcleanH1)
    (fun t => sload_hashLeafOut_of_clean t hcleanH3)
    -- allocator bounds
    hplowW
    (by omega)
    hplowN
    (show ((wS2 evm V IX k).mload 64).val + 128 ≤ 2 ^ 256 by omega)
    -- cleanliness
    hclean4 hcleanF hcleanV hcleanB1 hcleanB2 hcleanA1 hcleanA2
    -- account presence
    haccEK haccFK haccH3
    -- small element indices
    hIXlow hnidx
    -- the quad-anchor pack (drop the entry anchor)
    (by
      intro m hm
      rw [guards_sload hcleanG 1] at hm
      obtain ⟨wm, _, h2, h3, h4, h5, h6, h7⟩ := hcach m hm
      exact ⟨wm, h2, h3, h4, h5, h6, h7⟩)
    -- decode injectivity, transported to G
    (by
      intro m hm m' hm' heq
      rw [guards_sload hcleanG 1] at hm hm'
      refine hinj m hm m' hm' ?_
      rw [← hdecGm m (le_of_lt hm), ← hdecGm m' (le_of_lt hm')]
      exact heq)
    -- low-slot packs
    hok₁ hokp hok₂
  -- ===== weld: the concrete final state IS the glueSeq' chain =====
  calc leafSetOf (wFinal evm V IX k k2 k3)
      = imtInsert (leafSetOf (guardsEvm evm V IX))
          (decodeLeaf (guardsEvm evm V IX) IX) V := hmain
    _ = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
        rw [hsetG, hdIX]


set_option maxHeartbeats 1600000 in
/-- **THE EVOLUTION STEP, AXIOM-FREE.**  `insertGlue_evolution`'s only axiom source is its
`insertGlue_leafSetOf` call; everything else in it is membership, window-order and freshness
reasoning that never touches a slot.  So the twin forwards, and inherits the entry-state-only
hypothesis shape. -/
theorem insertGlue_evolution_of_config
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    -- the five pool/window facts, at the ENTRY state only
    (hsepE : Clear.KeccakSlotSep.Separated evm)
    (husedE : Clear.KeccakFresh.CacheInUsed evm)
    (hinjE : Clear.KeccakFresh.CacheInj evm)
    (hRwE : Clear.KeccakLowSlot.RangeInWindow evm)
    (hCwE : Clear.KeccakLowSlot.CachedInWindow evm)
    -- window guard + count arithmetic (entry state)
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    -- WHAT THE GUARDS PIN: the value-order gate (strict lower edge) and
    -- the search loop's break (weak upper edge) — `insertGlue_prefix`'s
    -- `hvo`/`hwin`, definitionally (guardsEvm/guardsLM are reducible)
    (hvo : (guardsEvm evm V IX).mload (guardsLM evm V IX) < V)
    (hwin : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64) = 0
        ∨ ¬ ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64) < V))
    -- the abstract list invariants (see the section header)
    (hclosed : NextClosed (leafSetOf evm))
    (hfresh : V ∉ IMTAbstract.keys (leafSetOf evm))
    -- guards-stage accessor cleanliness (vti read + leaves read)
    (hcleanG : (accOut (accOut evm V 5).2 IX 4).2.hash_collision = false)
    -- allocator bounds (hpG/hpW/hpN as in `insertGlue_prefix`, plus floors)
    (hpG : (((accOut (accOut evm V 5).2 IX 4).2).mload 64).val + 96
        ≤ 18446744073709551615)
    (hpW : ((guardsEvm evm V IX).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowW : 96 ≤ ((guardsEvm evm V IX).mload 64).val)
    (hpN : ((wS2 evm V IX k).mload 64).val + 96 ≤ 18446744073709551615)
    (hplowN : 96 ≤ ((wS2 evm V IX k).mload 64).val)
    -- cleanliness of the write-stage keccak steps
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
    -- account presence where `sstore` must not be a no-op
    (haccEK : (((accOut (wE4 evm V IX) IX 4).2).lookupAccount
        ((accOut (wE4 evm V IX) IX 4).2).execution_env.code_owner).isSome)
    (haccFK : (((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).lookupAccount
        ((accOut (wF4 evm V IX k) (evm.sload 1) 4).2).execution_env.code_owner).isSome)
    (haccH3 : ((wH3 evm V IX k).lookupAccount
        (wH3 evm V IX k).execution_env.code_owner).isSome)
    -- the level-0 element indices are small
    (hIXlow : IX.val < Clear.KeccakInjective.lowSlotBound)
    (hnidx : ((wH3 evm V IX k).sload 1).val < Clear.KeccakInjective.lowSlotBound)
    -- THE FIVE-ANCHOR CACHE PACK (entry / guards / E4 / F4 / H3)
    (hcach : ∀ m : ℕ, m ≤ (evm.sload 1).val → ∃ wm,
      Finmap.lookup (accInterval evm (m : UInt256) 4) evm.keccak_map = some wm
      ∧ Finmap.lookup (accInterval (guardsEvm evm V IX) (m : UInt256) 4)
          (guardsEvm evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wE4 evm V IX).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wF4 evm V IX k) (m : UInt256) 4)
          (wF4 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wH3 evm V IX k) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wH1 evm V IX).keccak_map = some wm)
    -- decode injectivity below the count, at the entry state
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    -- the walks' low-slot packs (concrete walk states)
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j)) :
    decodeLeaf evm IX ∈ leafSetOf evm
    ∧ (decodeLeaf evm IX).key < V
    ∧ ((decodeLeaf evm IX).nextKey = 0 ∨ V < (decodeLeaf evm IX).nextKey)
    ∧ leafSetOf (wFinal evm V IX k k2 k3)
        = imtInsert (leafSetOf evm) (decodeLeaf evm IX) V := by
  have hwlt : IX.val < (evm.sload 1).val := hbound
  -- ===== MEMBERSHIP: the window leaf is in the abstract set =====
  have hmem : decodeLeaf evm IX ∈ leafSetOf evm := by
    unfold leafSetOf
    exact Finset.mem_image.mpr
      ⟨IX.val, Finset.mem_range.mpr hwlt, by rw [Fin.cast_val_eq_self]⟩
  -- ===== the guards-stage read-backs (as in the weld) =====
  have hdIX : decodeLeaf (guardsEvm evm V IX) IX = decodeLeaf evm IX := by
    obtain ⟨wm, h0, hG, _, _, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at h0 hG
    unfold decodeLeaf
    rw [(leafSlot_keccak hG).2, (leafSlot_keccak h0).2,
        guards_sload hcleanG wm, guards_sload hcleanG (wm + 2)]
  have hkeyG : (guardsEvm evm V IX).mload (guardsLM evm V IX)
      = (decodeLeaf (guardsEvm evm V IX) IX).key := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1) :=
      leafRead_mload_key hpG
    have hdk : (decodeLeaf (guardsEvm evm V IX) IX).key
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX) := rfl
    rw [hr, hdk, hslotG]
    rfl
  have hnvG : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
      = (decodeLeaf (guardsEvm evm V IX) IX).nextKey := by
    obtain ⟨wIX, hIX0, hIXG, _, _, _, _, _⟩ := hcach IX.val (le_of_lt hwlt)
    rw [Fin.cast_val_eq_self IX] at hIX0 hIXG
    have hw : wIX = (accOut (accOut evm V 5).2 IX 4).1 :=
      guards_slot_pins hcleanG hIX0
    have hslotG : leafSlot (guardsEvm evm V IX) IX
        = (accOut (accOut evm V 5).2 IX 4).1 := by
      rw [← hw]
      exact (leafSlot_keccak hIXG).2
    have hr : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64)
        = ((accOut (accOut evm V 5).2 IX 4).2).sload
            ((accOut (accOut evm V 5).2 IX 4).1 + 2) :=
      leafRead_mload_nextKey hpG
    have hdn : (decodeLeaf (guardsEvm evm V IX) IX).nextKey
        = (guardsEvm evm V IX).sload (leafSlot (guardsEvm evm V IX) IX + 2) := rfl
    rw [hr, hdn, hslotG]
    rfl
  -- ===== WINDOW FACT 1: the strict lower edge (value-order gate) =====
  have hlow : (decodeLeaf evm IX).key < V := by
    rw [← hdIX, ← hkeyG]
    exact hvo
  -- ===== WINDOW FACT 2: the weak upper edge (search-loop break) =====
  have hweak : (decodeLeaf evm IX).nextKey = 0
      ∨ V ≤ (decodeLeaf evm IX).nextKey := by
    rw [← hdIX, ← hnvG]
    rcases hwin with h0 | hge
    · exact Or.inl h0
    · exact Or.inr (not_lt.mp hge)
  -- ===== STRICTNESS UPGRADE: freshness excludes `V = nextKey` =====
  have hstrict : (decodeLeaf evm IX).nextKey = 0
      ∨ V < (decodeLeaf evm IX).nextKey :=
    window_strict_of_not_mem hclosed hmem hfresh hweak
  -- ===== PACKAGE with the weld's set equation =====
  exact ⟨hmem, hlow, hstrict,
    insertGlue_leafSetOf_of_config hsepE husedE hinjE hRwE hCwE
      hbound hnw hcleanG hpG hpW hplowW hpN hplowN
      hclean4 hcleanF hcleanV hcleanH1 hcleanH3 hcleanB1 hcleanB2 hcleanA1
      hcleanA2 haccEK haccFK haccH3 hIXlow hnidx hcach hinj hok₁ hokp hok₂⟩


open Clear.KeccakDeterminism in
set_option maxHeartbeats 1600000 in
/-- **The Evolution insert disjunct, AXIOM-FREE** — `insertGlue_evolution_step` verbatim, on
the derived route.  This is the top of the insert-fidelity chain: the shape
`IMTAbstract.Evolution`'s insert disjunct consumes, now resting on nothing but the five
pool/window facts at the dispatcher entry state. -/
theorem insertGlue_evolution_step_of_config
    {evm : EVMState} {V IX : UInt256} {k k2 k3 : ℕ}
    -- the five pool/window facts, at the ENTRY state only
    (hsepE : Clear.KeccakSlotSep.Separated evm)
    (husedE : Clear.KeccakFresh.CacheInUsed evm)
    (hinjE : Clear.KeccakFresh.CacheInj evm)
    (hRwE : Clear.KeccakLowSlot.RangeInWindow evm)
    (hCwE : Clear.KeccakLowSlot.CachedInWindow evm)
    (hbound : IX < evm.sload 1)
    (hnw : (evm.sload 1).val + 1 < 2 ^ 256)
    (hvo : (guardsEvm evm V IX).mload (guardsLM evm V IX) < V)
    (hwin : (guardsEvm evm V IX).mload (guardsLM evm V IX + 64) = 0
        ∨ ¬ ((guardsEvm evm V IX).mload (guardsLM evm V IX + 64) < V))
    (hclosed : NextClosed (leafSetOf evm))
    (hfresh : V ∉ IMTAbstract.keys (leafSetOf evm))
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
          (wH3 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wH3 evm V IX k).keccak_map = some wm
      ∧ Finmap.lookup (accInterval (wE4 evm V IX) (m : UInt256) 4)
          (wH1 evm V IX).keccak_map = some wm)
    (hinj : ∀ m : ℕ, m < (evm.sload 1).val → ∀ m' : ℕ, m' < (evm.sload 1).val →
      decodeLeaf evm (m : UInt256) = decodeLeaf evm (m' : UInt256) → m = m')
    (hok₁ : ∀ j, j < k → StepLowOK 0 2
        (updTreeW (wS1 evm V IX) ((guardsEvm evm V IX).mload 64) IX j))
    (hokp : ∀ j, j < k2 → PadLowOK
        (pushPadW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) j))
    (hok₂ : ∀ j, j < k3 → StepLowOK 0 ((0 : UInt256) + 2)
        (pushOutW (wS3 evm V IX k) ((wS2 evm V IX k).mload 64) k2 j)) :
    ∃ W₀ v', W₀ ∈ leafSetOf evm ∧ W₀.key < v'
      ∧ (W₀.nextKey = 0 ∨ v' < W₀.nextKey)
      ∧ leafSetOf (wFinal evm V IX k k2 k3)
          = imtInsert (leafSetOf evm) W₀ v' := by
  obtain ⟨hmem, hlow, hstrict, hset⟩ :=
    insertGlue_evolution_of_config hsepE husedE hinjE hRwE hCwE hbound hnw hvo hwin
    hclosed hfresh hcleanG hpG hpW hplowW hpN hplowN hclean4 hcleanF hcleanV
    hcleanH1 hcleanH3 hcleanB1 hcleanB2 hcleanA1 hcleanA2 haccEK haccFK haccH3
    hIXlow hnidx hcach hinj hok₁ hokp hok₂
  exact ⟨decodeLeaf evm IX, V, hmem, hlow, hstrict, hset⟩

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
