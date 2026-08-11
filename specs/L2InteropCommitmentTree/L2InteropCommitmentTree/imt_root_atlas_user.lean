/-
  ⚠️  THIS FILE DOES NOT COMPILE — ITS 72 RESULTS ARE UNVERIFIED.  ⚠️

  Discovered 2026-08-11 by `scripts/axiom-sweep.sh`, which could not sweep this directory because
  importing this module fails.  `lake build --old specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_root_atlas_user`
  reported 5 errors.  **4 remain** (updated 2026-08-11 after reconstructing the missing helper):

    * ~~unknown identifier `byte_mstore32_pinned`~~ — FIXED: reconstructed below from its use site.
      The name existed nowhere in the corpus, so it was a deleted helper, not a mappable rename; the
      statement it had to have is forced by the goal, and it follows from
      `KeccakDeterminism.lookup_updateMemory_at` with no new reasoning.
    * line ~1053  whnf timeout at 4,000,000 heartbeats, on the `show` in `stepOdd_hit_atlas` that
                  states `stepOdd_hit`'s post-state as an explicit `nodeStore` term
    * lines ~1072+  `rewrite` failures against `nodeStore` in `stepOdd_hit_sload`

  Both remaining errors are in the same two theorems and have the same shape: a hand-written `show`
  or `rw` asserting the exact form of a `stepOdd` post-state.  If that form has drifted from what
  `stepOdd_hit` now produces, defeq has to grind through the whole term — the signature of a state
  mismatch rather than a missing fact (see the note in `AGENTS.md` gap 0).

  STATUS.  No `.olean` has ever been produced for it, and nothing imports it (the only other mention
  in the corpus is a prose reference in `specs/KeccakSlotSep.lean`).  `SECURITY_VERIFICATION.md` does
  not cite it, so no headline claim rests on it.  But the `specs` lean_lib has root `specs`, so it IS
  nominally in the build target — it is unbuilt only because a full `lake build specs` is impractical
  and nobody compiled this file individually.

  WHY THE BANNER RATHER THAN A FIX OR A DELETION.  Deleting is not mine to decide, and the errors are
  substantive rather than cosmetic (a deleted helper plus an elaboration wall).  What matters
  immediately is that a reader browsing this directory has no other way to tell these 72 theorems are
  unverified — every other file here compiles.

  This is the third instance of the regression class `SECURITY_VERIFICATION.md`'s hygiene note already
  records: `lake env lean` does not check import-olean freshness, so a renamed or deleted helper can
  silently break a file that nothing happens to import.
-/

import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_fidelity_user

/-
  ROOT FIDELITY, stages R0 + R1 — the `arrInterval` transport kit and the
  cached-hit node-atlas reads (ROOT_FIDELITY_BLUEPRINT.md §1.3, §2).

  THE MODEL ARTIFACT THIS FILE TAMES.  The storage-array accessor
  (`arrOut σ a = keccak256` of the 32-byte scratch after `mstore 0 a`) keys
  the keccak cache on `mkInterval (σ.mstore 0 a).machine_state 0 32` — the
  32 *word* reads at byte addresses `0..31`, which touch memory bytes
  `[0, 62]`.  The `mstore 0 a` pins bytes `[0, 32)`; bytes `[32, 62]` are
  JUNK inherited from the state.  Consequently:

  * the interval is invariant under `sstore` (memory untouched), under
    `mstore 0 _` (self-overwrite — the next accessor repins the same
    window), under any `mstore` at byte address `≥ 63` (allocator bumps
    write at `≥ 64`), and under `keccak256` itself (no memory effect);
  * the interval is **NOT** invariant under `mstore 32 _`: every `accOut`
    pair-hash step (`mstore 0 a; mstore 32 b; keccak`) rewrites bytes
    `[32, 63]` and hence CHANGES every array-accessor cache key.  This is
    the ANCHOR BOUNDARY — deliberately no lemma; after a hash step the
    junk `[32, 62]` is a pure function of the stored word `b`
    (`arrInterval_mstore32_pinned` below), and re-anchoring the atlas
    there needs fresh cache entries from the history (R2's business).

  DESIGN (the §4.1 iteration, settled here).  `AtlasCachedAt σ A H` is
  **self-anchored**: all three entry families are keyed on intervals of
  `σ` itself — `σ` carries its own junk, so the predicate is
  "junk-parametric" by construction.  The nested accessor chains
  (`sibRead` = `arrOut` after `arrOut`) collapse onto the same anchor
  because the inner call's scratch state differs from `σ` only by
  `mstore 0` writes and cache-neutral keccak steps, and `arrInterval` is
  invariant under exactly those (`arrInterval_mstore0`,
  `arrInterval_keccakOut`).  No fixed-scratch-state expressions (as in the
  blueprint's first sketch) are needed.

  Contents:
  * R0 — `arrInterval` + the transport kit (`arrInterval_eq_of_junk_agree`,
    `_sstore`, `_mstore0`, `_mstore_high`, `_keccakOut`, `_arrOut`,
    `_mstore32_pinned`, `arrInterval_ne_of_slot_ne`);
  * the atlas (`NodeAtlas`, `AtlasCachedAt`, `nodeAt`/`lenAt`/`zeroAt`/
    `rootSlot`) and its predicate transports (`atlas_sstore`,
    `atlas_mstore0`, `atlas_mstore_high`, `atlas_keccakOut`, `atlas_arrOut`,
    `atlas_of_junk_agree`);
  * R1 — cached-hit closed forms of every storage-array primitive of the
    walk (`arrOut`, `sibRead`, `sideRead`, `lenRead`, `nodeStore`,
    `leafWriteEvm`, `pushEvm`, `padStep`, root readback) and the slot
    separations (level-vs-level, in-level, vs the header/zeros families,
    vs reserved low slots).

  Axiom base: the R1 separations use the trusted keccak idealizations
  (`keccak256_inj`-family); everything else is standard-trio only.
-/

namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local model helpers (private copies of helpers private elsewhere) -/

private lemma uint256_size_eq : UInt256.size = 2 ^ 256 := by norm_num

private lemma val_0 : ((0 : UInt256)).val = 0 := by decide

private lemma val_32 : ((32 : UInt256)).val = 32 := by decide

private lemma val_coe_add (k : ℕ) (a : UInt256) (hk : k < 32)
    (ha : a.val + 32 ≤ 2 ^ 256) :
    (((↑k : UInt256) + a)).val = k + a.val := by
  have hs := uint256_size_eq
  have hks : k < UInt256.size := by omega
  have hkv : ((↑k : UInt256)).val = k := Fin.val_cast_of_lt hks
  have h1 : (((↑k : UInt256) + a)).val
      = (((↑k : UInt256)).val + a.val) % UInt256.size := rfl
  rw [h1, hkv]
  exact Nat.mod_eq_of_lt (by omega)

private lemma natCast_val {n : ℕ} (h : n < 2 ^ 256) : ((n : UInt256)).val = n :=
  Fin.val_cast_of_lt (by rw [uint256_size_eq]; exact h)

private lemma level_cast_val {l H : ℕ} (hl : l ≤ H) (hH : H < 2 ^ 32) :
    ((l : UInt256)).val = l :=
  natCast_val (lt_trans (lt_of_le_of_lt hl hH) (by norm_num))

/-- `sstore` touches accounts and `used_range` only — memory is unchanged. -/
private lemma ms_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).machine_state = σ.machine_state := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- `sstore` leaves the keccak cache unchanged. -/
private lemma kmap_sstore (σ : EVMState) (a v : UInt256) :
    (σ.sstore a v).keccak_map = σ.keccak_map := by
  unfold EVMState.sstore
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-- `sstore` and `mstore` commute (they update disjoint components). -/
private lemma sstore_mstore_comm (σ : EVMState) (a b s v : UInt256) :
    (σ.mstore a b).sstore s v = (σ.sstore s v).mstore a b := by
  unfold EVMState.sstore
  have hlk : (σ.mstore a b).lookupAccount (σ.mstore a b).execution_env.code_owner
      = σ.lookupAccount σ.execution_env.code_owner := rfl
  rw [hlk]
  cases σ.lookupAccount σ.execution_env.code_owner with
  | none => rfl
  | some act => rfl

/-! ## R0 — the accessor interval and its transport kit -/

/-- The keccak preimage interval of one array-accessor step (`arrOut σ a` =
`keccak256` of scratch `[0, 32)` after `mstore 0 a`): the 32 word reads at
byte addresses `0..31`, depending on memory bytes `[0, 62]` — of which
`[0, 32)` are pinned to `a` and `[32, 62]` are the state's junk. -/
def arrInterval (σ : EVMState) (a : UInt256) : List UInt256 :=
  mkInterval (σ.mstore 0 a).machine_state 0 32

/-- Byte agreement after the accessor's `mstore 0 a`: bytes `< 32` are
pinned by `a`, bytes in `[32, 62]` fall through to the frame. -/
private lemma byte_mstore0_eq
    {σ₁ σ₂ : EVMState} {a : UInt256} {i : UInt256}
    (hi : i.val ≤ 62)
    (hframe : 32 ≤ i.val →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory) :
    Finmap.lookup i (σ₁.mstore 0 a).machine_state.memory
      = Finmap.lookup i (σ₂.mstore 0 a).machine_state.memory := by
  have hms : ∀ σ : EVMState, (σ.mstore 0 a).machine_state
      = σ.machine_state.updateMemory 0 a := fun _ => rfl
  rw [hms σ₁, hms σ₂]
  rcases Nat.lt_or_ge i.val 32 with h32 | h32
  · -- window byte: determined by `a` on both sides
    have hin : i = (↑(i.val) : UInt256) + 0 := by
      rw [add_zero, Fin.cast_val_eq_self]
    rw [hin,
        lookup_updateMemory_at _ 0 a i.val h32 window_zero_nodup,
        lookup_updateMemory_at _ 0 a i.val h32 window_zero_nodup]
  · -- junk byte: outside the window on both sides → frame hypothesis
    have hout0 : ∀ k : ℕ, k < 32 → i ≠ (↑k : UInt256) + 0 := by
      intro k hk he
      have : i.val = k + 0 := by
        rw [he, val_coe_add k 0 hk (by rw [val_0]; norm_num)]
        rw [val_0]
      omega
    rw [lookup_updateMemory_outside _ 0 a i hout0,
        lookup_updateMemory_outside _ 0 a i hout0]
    exact hframe h32

/-- **Frame-conditioned accessor-interval equality** (the `[0, 62]`-window
analog of `accessor_interval_eq`): two states that agree on the junk bytes
`[32, 62]` produce equal `arrInterval`s for every slot `a`. -/
theorem arrInterval_eq_of_junk_agree
    {σ₁ σ₂ : EVMState} {a : UInt256}
    (hframe : ∀ i : UInt256, 32 ≤ i.val → i.val ≤ 62 →
      Finmap.lookup i σ₁.machine_state.memory
        = Finmap.lookup i σ₂.machine_state.memory) :
    arrInterval σ₁ a = arrInterval σ₂ a := by
  unfold arrInterval
  apply mkInterval_eq_of_byte_agree (hnw := by rw [val_0, val_32]; norm_num)
  intro i _ h1
  rw [val_0, val_32] at h1
  exact byte_mstore0_eq (by omega)
    (fun h32 => hframe i h32 (by omega))

/-- `arrInterval` depends only on the machine state. -/
theorem arrInterval_machine_congr {σ₁ σ₂ : EVMState} {a : UInt256}
    (h : σ₁.machine_state = σ₂.machine_state) :
    arrInterval σ₁ a = arrInterval σ₂ a := by
  unfold arrInterval
  show mkInterval (σ₁.machine_state.updateMemory 0 a) 0 32
      = mkInterval (σ₂.machine_state.updateMemory 0 a) 0 32
  rw [h]

/-- **(i)** `arrInterval` is invariant under any `sstore`. -/
theorem arrInterval_sstore (σ : EVMState) (s v a : UInt256) :
    arrInterval (σ.sstore s v) a = arrInterval σ a :=
  arrInterval_machine_congr (ms_sstore σ s v)

/-- **(iii)** `arrInterval` is invariant under `mstore 0` (self-overwrite:
the accessor repins the whole `[0, 32)` window). -/
theorem arrInterval_mstore0 (σ : EVMState) (b a : UInt256) :
    arrInterval (σ.mstore 0 b) a = arrInterval σ a := by
  apply arrInterval_eq_of_junk_agree
  intro i h32 _
  show Finmap.lookup i (σ.machine_state.updateMemory 0 b).memory
      = Finmap.lookup i σ.machine_state.memory
  rw [lookup_updateMemory_outside_val σ.machine_state 0 b i
      (by rw [val_0]; norm_num)
      (Or.inr (by rw [val_0]; omega))]

/-- **(ii)** `arrInterval` is invariant under `mstore` at byte addresses
`≥ 63` — in particular under the allocator bumps (`mstore 64 _`). -/
theorem arrInterval_mstore_high (σ : EVMState) (b v a : UInt256)
    (hb : 63 ≤ b.val) (hnw : b.val + 32 ≤ 2 ^ 256) :
    arrInterval (σ.mstore b v) a = arrInterval σ a := by
  apply arrInterval_eq_of_junk_agree
  intro i _ h62
  show Finmap.lookup i (σ.machine_state.updateMemory b v).memory
      = Finmap.lookup i σ.machine_state.memory
  rw [lookup_updateMemory_outside_val σ.machine_state b v i hnw
      (Or.inl (by omega))]

/-- `arrInterval` is invariant under any `keccak256` step (no memory
effect in every branch). -/
theorem arrInterval_keccakOut (σ : EVMState) (p n a : UInt256) :
    arrInterval (keccakOut σ p n).2 a = arrInterval σ a :=
  arrInterval_machine_congr (keccakOut_machine_state σ p n)

/-- `arrInterval` is invariant under a whole `arrOut` step (`mstore 0` +
keccak). -/
theorem arrInterval_arrOut (σ : EVMState) (b a : UInt256) :
    arrInterval (arrOut σ b).2 a = arrInterval σ a := by
  have h1 : arrInterval (arrOut σ b).2 a = arrInterval (σ.mstore 0 b) a :=
    arrInterval_machine_congr (keccakOut_machine_state (σ.mstore 0 b) 0 32)
  rw [h1, arrInterval_mstore0]

/-- **The anchor boundary, quantified** (R2 seed): `arrInterval` is *not*
invariant under `mstore 32` — but after the accessor-shaped double write
(`mstore 0 x; mstore 32 b`) the junk `[32, 62]` is a pure function of `b`,
so any two states land on the SAME interval once they store the same `b`.
This is the re-anchoring fact a walk-level atlas transport (R2) keys on:
after a pair-hash step the atlas intervals depend only on the running
accumulator, not on the pre-step junk. -/
theorem arrInterval_mstore32_pinned
    {σ₁ σ₂ : EVMState} (x y b a : UInt256) :
    arrInterval ((σ₁.mstore 0 x).mstore 32 b) a
      = arrInterval ((σ₂.mstore 0 y).mstore 32 b) a := by
  apply arrInterval_eq_of_junk_agree
  intro i h32 h62
  show Finmap.lookup i
        ((σ₁.machine_state.updateMemory 0 x).updateMemory 32 b).memory
      = Finmap.lookup i
        ((σ₂.machine_state.updateMemory 0 y).updateMemory 32 b).memory
  have hin : i = (↑(i.val - 32) : UInt256) + 32 := by
    apply Fin.ext
    rw [val_coe_add (i.val - 32) 32 (by omega) (by rw [val_32]; norm_num),
        val_32]
    omega
  rw [hin,
      lookup_updateMemory_at _ 32 b (i.val - 32) (by omega) window_32_nodup,
      lookup_updateMemory_at _ 32 b (i.val - 32) (by omega) window_32_nodup]

/-! ### Interval disagreement via the word-0 readback -/

/-- Element 0 of a `[0, 32)` interval is the word at address 0. -/
private lemma mkInterval_0_32_get0 (ms : MachineState) :
    (mkInterval ms 0 32).get? 0 = some (ms.lookupMemory (0 : UInt256)) := by
  unfold EVMState.mkInterval
  simp only [List.get?_map]
  rw [show (List.range' (((0 : UInt256)).val) (((32 : UInt256)).val)).get? 0
      = some 0 from by decide]
  rfl

/-- The accessor scratch reads its own slot word back at address 0. -/
private lemma mstore0_readback (σ : EVMState) (a : UInt256) :
    (σ.mstore 0 a).machine_state.lookupMemory (0 : UInt256) = a := by
  show (σ.machine_state.updateMemory 0 a).lookupMemory (0 : UInt256) = a
  exact lookupMemory_updateMemory_self' _ 0 a (by rw [val_0]; norm_num)

private lemma arrInterval_word0 (σ : EVMState) (a : UInt256) :
    (arrInterval σ a).get? 0 = some a := by
  show (mkInterval (σ.mstore 0 a).machine_state 0 32).get? 0 = some a
  rw [mkInterval_0_32_get0, mstore0_readback]

/-- **Accessor intervals of distinct slots differ** (in any pair of
states): the slot word is pinned at element 0. -/
theorem arrInterval_ne_of_slot_ne {σ₁ σ₂ : EVMState} {a b : UInt256}
    (hab : a ≠ b) :
    arrInterval σ₁ a ≠ arrInterval σ₂ b := by
  intro heq
  apply hab
  have h₁ := arrInterval_word0 σ₁ a
  rw [heq, arrInterval_word0 σ₂ b] at h₁
  exact (Option.some.inj h₁).symm

/-! ## The node atlas

State-independent NAMES for the `_nodes`/`_zeros` slot families
(storage layout: `_nodes` outer at slot 2, `_zeros` at slot 3):

* `A.w2   = keccak(2)`     — `_nodes` outer data base; level-`l` inner
  header (length) at `A.w2 + l`;
* `A.wl l = keccak(w2+l)`  — level-`l` inner data base; element `j` at
  `A.wl l + j`;
* `A.wz   = keccak(3)`     — `_zeros` data base; `_zeros[l]` at `A.wz + l`.
-/

structure NodeAtlas where
  w2 : UInt256
  wl : ℕ → UInt256
  wz : UInt256

/-- **The atlas-cached predicate** (self-anchored, junk-parametric through
`σ` itself): the three accessor-interval families of `σ` are cached to the
atlas names.  Every R1 read below is a cache HIT under this predicate — no
fresh keccak draws, no `used_range` movement, evm effects = scratch
`mstore 0`s only. -/
def AtlasCachedAt (σ : EVMState) (A : NodeAtlas) (H : ℕ) : Prop :=
  Finmap.lookup (arrInterval σ 2) σ.keccak_map = some A.w2
  ∧ Finmap.lookup (arrInterval σ 3) σ.keccak_map = some A.wz
  ∧ ∀ l : ℕ, l ≤ H →
      Finmap.lookup (arrInterval σ (A.w2 + (l : UInt256))) σ.keccak_map
        = some (A.wl l)

/-- Stored node value: element `j` of the level-`l` inner array. -/
def nodeAt (σ : EVMState) (A : NodeAtlas) (l : ℕ) (j : UInt256) : UInt256 :=
  σ.sload (A.wl l + j)

/-- Stored level length: the level-`l` inner header. -/
def lenAt (σ : EVMState) (A : NodeAtlas) (l : ℕ) : UInt256 :=
  σ.sload (A.w2 + (l : UInt256))

/-- Stored `_zeros[l]`. -/
def zeroAt (σ : EVMState) (A : NodeAtlas) (l : UInt256) : UInt256 :=
  σ.sload (A.wz + l)

/-- The root slot: element 0 of the level-`H` inner array. -/
def rootSlot (A : NodeAtlas) (H : ℕ) : UInt256 := A.wl H

/-! ### Predicate transports (which steps the atlas survives)

The atlas survives `sstore`s, scratch `mstore 0`s, allocator-style
`mstore ≥ 63`s, and arbitrary keccak steps.  It does **not** survive
`mstore 32` (the `accOut` anchor boundary) — re-anchoring there is R2's
job, via `arrInterval_mstore32_pinned` + history-supplied cache entries. -/

/-- Generic transport: junk agreement on `[32, 62]` + cache monotonicity. -/
theorem atlas_of_junk_agree {σ σ' : EVMState} {A : NodeAtlas} {H : ℕ}
    (hframe : ∀ i : UInt256, 32 ≤ i.val → i.val ≤ 62 →
      Finmap.lookup i σ.machine_state.memory
        = Finmap.lookup i σ'.machine_state.memory)
    (hmono : ∀ (I : List UInt256) (w : UInt256),
      Finmap.lookup I σ.keccak_map = some w →
        Finmap.lookup I σ'.keccak_map = some w)
    (hA : AtlasCachedAt σ A H) : AtlasCachedAt σ' A H := by
  unfold AtlasCachedAt at hA ⊢
  obtain ⟨h2, h3, hw⟩ := hA
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · rw [← arrInterval_eq_of_junk_agree hframe]
    exact hmono _ _ h2
  · rw [← arrInterval_eq_of_junk_agree hframe]
    exact hmono _ _ h3
  · rw [← arrInterval_eq_of_junk_agree hframe]
    exact hmono _ _ (hw l hl)

/-- The atlas survives any `sstore`. -/
theorem atlas_sstore {σ : EVMState} {A : NodeAtlas} {H : ℕ} (s v : UInt256)
    (hA : AtlasCachedAt σ A H) : AtlasCachedAt (σ.sstore s v) A H := by
  unfold AtlasCachedAt at hA ⊢
  obtain ⟨h2, h3, hw⟩ := hA
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · rw [kmap_sstore, arrInterval_sstore]; exact h2
  · rw [kmap_sstore, arrInterval_sstore]; exact h3
  · rw [kmap_sstore, arrInterval_sstore]; exact hw l hl

/-- The atlas survives a scratch `mstore 0`. -/
theorem atlas_mstore0 {σ : EVMState} {A : NodeAtlas} {H : ℕ} (b : UInt256)
    (hA : AtlasCachedAt σ A H) : AtlasCachedAt (σ.mstore 0 b) A H := by
  unfold AtlasCachedAt at hA ⊢
  obtain ⟨h2, h3, hw⟩ := hA
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · rw [keccak_map_mstore, arrInterval_mstore0]; exact h2
  · rw [keccak_map_mstore, arrInterval_mstore0]; exact h3
  · rw [keccak_map_mstore, arrInterval_mstore0]; exact hw l hl

/-- The atlas survives an allocator-style `mstore` at address `≥ 63`. -/
theorem atlas_mstore_high {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (b v : UInt256) (hb : 63 ≤ b.val) (hnw : b.val + 32 ≤ 2 ^ 256)
    (hA : AtlasCachedAt σ A H) : AtlasCachedAt (σ.mstore b v) A H := by
  unfold AtlasCachedAt at hA ⊢
  obtain ⟨h2, h3, hw⟩ := hA
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · rw [keccak_map_mstore, arrInterval_mstore_high σ b v _ hb hnw]; exact h2
  · rw [keccak_map_mstore, arrInterval_mstore_high σ b v _ hb hnw]; exact h3
  · rw [keccak_map_mstore, arrInterval_mstore_high σ b v _ hb hnw]
    exact hw l hl

/-- The atlas survives any keccak step (fresh, hit, or collision): memory
untouched, cache only grows. -/
theorem atlas_keccakOut {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (p n : UInt256)
    (hA : AtlasCachedAt σ A H) : AtlasCachedAt (keccakOut σ p n).2 A H := by
  unfold AtlasCachedAt at hA ⊢
  obtain ⟨h2, h3, hw⟩ := hA
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · rw [arrInterval_keccakOut]; exact keccakOut_lookup_mono h2
  · rw [arrInterval_keccakOut]; exact keccakOut_lookup_mono h3
  · rw [arrInterval_keccakOut]; exact keccakOut_lookup_mono (hw l hl)

/-- The atlas survives a whole `arrOut` step. -/
theorem atlas_arrOut {σ : EVMState} {A : NodeAtlas} {H : ℕ} (b : UInt256)
    (hA : AtlasCachedAt σ A H) : AtlasCachedAt (arrOut σ b).2 A H := by
  show AtlasCachedAt (keccakOut (σ.mstore 0 b) 0 32).2 A H
  exact atlas_keccakOut 0 32 (atlas_mstore0 b hA)

/-! ## R1 — cached-hit atlas reads -/

/-- Generic cached hit: an `arrOut` whose interval is cached returns the
cached word, evm effect = the scratch `mstore 0` only. -/
theorem arrOut_of_atlas_entry {σ : EVMState} {x r : UInt256}
    (h : Finmap.lookup (arrInterval σ x) σ.keccak_map = some r) :
    arrOut σ x = (r, σ.mstore 0 x) := by
  unfold arrOut
  apply keccakOut_of_cached
  show Finmap.lookup (arrInterval σ x) (σ.mstore 0 x).keccak_map = some r
  rw [keccak_map_mstore]
  exact h

/-- Generic cached success witness (for the injectivity layer): the
accessor's `keccak256` genuinely succeeds with the cached word and leaves
the scratch state unchanged. -/
theorem keccak_of_atlas_entry {σ : EVMState} {x r : UInt256}
    (h : Finmap.lookup (arrInterval σ x) σ.keccak_map = some r) :
    (σ.mstore 0 x).keccak256 0 32 = some (r, σ.mstore 0 x) := by
  apply keccak256_of_cached'
  show Finmap.lookup (arrInterval σ x) (σ.mstore 0 x).keccak_map = some r
  rw [keccak_map_mstore]
  exact h

/-- `arrOut σ 2` (the `_nodes` outer accessor) under the atlas. -/
theorem arrOut_cached_2 {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) :
    arrOut σ 2 = (A.w2, σ.mstore 0 2) :=
  arrOut_of_atlas_entry hA.1

/-- `arrOut σ 3` (the `_zeros` accessor) under the atlas. -/
theorem arrOut_cached_3 {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) :
    arrOut σ 3 = (A.wz, σ.mstore 0 3) :=
  arrOut_of_atlas_entry hA.2.1

/-- The inner (level) accessor under the atlas: it runs on the outer hit's
scratch state `σ.mstore 0 2`, whose junk `[32, 62]` is `σ`'s own — the
self-anchored entry applies through `arrInterval_mstore0`. -/
theorem arrOut_cached_level {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) :
    arrOut (σ.mstore 0 2) (A.w2 + (l : UInt256))
      = (A.wl l, (σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))) :=
  arrOut_of_atlas_entry ((atlas_mstore0 2 hA).2.2 l hl)

/-- **Level-length readback**: the header sload of the walk's bound checks
under the atlas. -/
theorem lenRead_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (x : UInt256) :
    (arrOut σ 2).2.sload ((arrOut σ 2).1 + x) = σ.sload (A.w2 + x) := by
  have h2f : (arrOut σ 2).1 = A.w2 := by rw [arrOut_cached_2 hA]
  have h2s : (arrOut σ 2).2 = σ.mstore 0 2 := by rw [arrOut_cached_2 hA]
  rw [h2s, h2f]
  simp only [sload_mstore]

/-- **`sibRead` under the atlas**: the two-level sibling read is a pure
`sload` at the atlas-named element slot; evm effect = the two scratch
`mstore 0`s. -/
theorem sibRead_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) (j : UInt256) :
    sibRead σ 2 (l : UInt256) j
      = (σ.sload (A.wl l + j),
         (σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))) := by
  have h2f : (arrOut σ 2).1 = A.w2 := by rw [arrOut_cached_2 hA]
  have h2s : (arrOut σ 2).2 = σ.mstore 0 2 := by rw [arrOut_cached_2 hA]
  have hLf : (arrOut (σ.mstore 0 2) (A.w2 + (l : UInt256))).1 = A.wl l := by
    rw [arrOut_cached_level hA hl]
  have hLs : (arrOut (σ.mstore 0 2) (A.w2 + (l : UInt256))).2
      = (σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256)) := by
    rw [arrOut_cached_level hA hl]
  unfold sibRead
  rw [h2s, h2f, hLf, hLs]
  simp only [sload_mstore]

/-- Value corollary of `sibRead_cached`. -/
theorem sibRead_cached_fst {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) (j : UInt256) :
    (sibRead σ 2 (l : UInt256) j).1 = σ.sload (A.wl l + j) := by
  rw [sibRead_cached hA hl j]

/-- **`sideRead` under the atlas**: the edge-branch `_zeros` read. -/
theorem sideRead_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (lvl : UInt256) :
    sideRead σ 3 lvl = (σ.sload (A.wz + lvl), σ.mstore 0 3) := by
  have h3f : (arrOut σ 3).1 = A.wz := by rw [arrOut_cached_3 hA]
  have h3s : (arrOut σ 3).2 = σ.mstore 0 3 := by rw [arrOut_cached_3 hA]
  unfold sideRead
  rw [h3s, h3f]
  simp only [sload_mstore]

/-- Value corollary of `sideRead_cached`. -/
theorem sideRead_cached_fst {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (lvl : UInt256) :
    (sideRead σ 3 lvl).1 = σ.sload (A.wz + lvl) := by
  rw [sideRead_cached hA lvl]

/-- **`nodeStore` under the atlas**, scratch-first shape: the parent store
is the `sstore` at the atlas-named element slot of the doubly-`mstore 0`d
state. -/
theorem nodeStore_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) {j v : UInt256} :
    nodeStore σ 2 (l : UInt256) j v
      = ((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).sstore
          (A.wl l + j) v := by
  have h2f : (arrOut σ 2).1 = A.w2 := by rw [arrOut_cached_2 hA]
  have h2s : (arrOut σ 2).2 = σ.mstore 0 2 := by rw [arrOut_cached_2 hA]
  have hLf : (arrOut (σ.mstore 0 2) (A.w2 + (l : UInt256))).1 = A.wl l := by
    rw [arrOut_cached_level hA hl]
  have hLs : (arrOut (σ.mstore 0 2) (A.w2 + (l : UInt256))).2
      = (σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256)) := by
    rw [arrOut_cached_level hA hl]
  unfold nodeStore
  rw [h2s, h2f, hLf, hLs]

/-- **`nodeStore` under the atlas, sstore-first normal form** — the shape
the walk lemmas consume: `= σ.sstore (A.wl l + j) v` up to the two
trailing scratch `mstore 0`s. -/
theorem nodeStore_cached' {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) {j v : UInt256} :
    nodeStore σ 2 (l : UInt256) j v
      = (((σ.sstore (A.wl l + j) v).mstore 0 2).mstore 0
          (A.w2 + (l : UInt256))) := by
  rw [nodeStore_cached hA hl]
  simp only [sstore_mstore_comm]

/-- Storage projection of `nodeStore` under the atlas: exactly one
`sstore`. -/
theorem nodeStore_cached_sload {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) {j v : UInt256}
    (s : UInt256) :
    (nodeStore σ 2 (l : UInt256) j v).sload s
      = (σ.sstore (A.wl l + j) v).sload s := by
  rw [nodeStore_cached' hA hl]
  simp only [sload_mstore]

/-- **`leafWriteEvm` under the atlas** (level-0 write of `updateLeaf`,
`ss = 0`): the leaf-hash store at element `idx` of level 0. -/
theorem leafWrite_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {idx leaf : UInt256} :
    leafWriteEvm σ 0 idx leaf
      = ((σ.mstore 0 2).mstore 0 A.w2).sstore (A.wl 0 + idx) leaf := by
  have h02 : (0 : UInt256) + 2 = 2 := by decide
  have h2f : (arrOut σ 2).1 = A.w2 := by rw [arrOut_cached_2 hA]
  have h2s : (arrOut σ 2).2 = σ.mstore 0 2 := by rw [arrOut_cached_2 hA]
  have hL := arrOut_cached_level (l := 0) hA (Nat.zero_le H)
  rw [Nat.cast_zero, add_zero] at hL
  have hLf : (arrOut (σ.mstore 0 2) A.w2).1 = A.wl 0 := by rw [hL]
  have hLs : (arrOut (σ.mstore 0 2) A.w2).2
      = (σ.mstore 0 2).mstore 0 A.w2 := by rw [hL]
  unfold leafWriteEvm
  rw [h02, h2s, h2f, hLf, hLs]

/-- `leafWriteEvm` under the atlas, sstore-first normal form. -/
theorem leafWrite_cached' {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {idx leaf : UInt256} :
    leafWriteEvm σ 0 idx leaf
      = ((σ.sstore (A.wl 0 + idx) leaf).mstore 0 2).mstore 0 A.w2 := by
  rw [leafWrite_cached hA]
  simp only [sstore_mstore_comm]

/-- Storage projection of the leaf write under the atlas. -/
theorem leafWrite_cached_sload {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {idx leaf : UInt256} (s : UInt256) :
    (leafWriteEvm σ 0 idx leaf).sload s
      = (σ.sstore (A.wl 0 + idx) leaf).sload s := by
  rw [leafWrite_cached' hA]
  simp only [sload_mstore]

/-- **`pushEvm` under the atlas** (the pad-walk push onto the level-`l`
array at header `A.w2 + l`): length bump at the header, element write at
`A.wl l + oldLen`; evm effect otherwise = one scratch `mstore 0`.  The
inner accessor hits because `arrInterval` is `sstore`-invariant (R0 (i)). -/
theorem pushEvm_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) {v : UInt256} :
    pushEvm σ (A.w2 + (l : UInt256)) v
      = ((σ.sstore (A.w2 + (l : UInt256))
            (σ.sload (A.w2 + (l : UInt256)) + 1)).mstore 0
              (A.w2 + (l : UInt256))).sstore
          (A.wl l + σ.sload (A.w2 + (l : UInt256))) v := by
  have hhit : arrOut (σ.sstore (A.w2 + (l : UInt256))
        (σ.sload (A.w2 + (l : UInt256)) + 1)) (A.w2 + (l : UInt256))
      = (A.wl l,
         (σ.sstore (A.w2 + (l : UInt256))
            (σ.sload (A.w2 + (l : UInt256)) + 1)).mstore 0
              (A.w2 + (l : UInt256))) :=
    arrOut_of_atlas_entry
      ((atlas_sstore (A.w2 + (l : UInt256))
          (σ.sload (A.w2 + (l : UInt256)) + 1) hA).2.2 l hl)
  have hf : (arrOut (σ.sstore (A.w2 + (l : UInt256))
        (σ.sload (A.w2 + (l : UInt256)) + 1)) (A.w2 + (l : UInt256))).1
      = A.wl l := by rw [hhit]
  have hs : (arrOut (σ.sstore (A.w2 + (l : UInt256))
        (σ.sload (A.w2 + (l : UInt256)) + 1)) (A.w2 + (l : UInt256))).2
      = (σ.sstore (A.w2 + (l : UInt256))
            (σ.sload (A.w2 + (l : UInt256)) + 1)).mstore 0
              (A.w2 + (l : UInt256)) := by rw [hhit]
  unfold pushEvm
  rw [hs, hf]

/-- `pushEvm` under the atlas, sstore-first normal form: bump then element
write, one trailing scratch `mstore 0`. -/
theorem pushEvm_cached' {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) {v : UInt256} :
    pushEvm σ (A.w2 + (l : UInt256)) v
      = (((σ.sstore (A.w2 + (l : UInt256))
            (σ.sload (A.w2 + (l : UInt256)) + 1)).sstore
          (A.wl l + σ.sload (A.w2 + (l : UInt256))) v).mstore 0
            (A.w2 + (l : UInt256))) := by
  rw [pushEvm_cached hA hl]
  simp only [sstore_mstore_comm]

/-- Storage projection of `pushEvm` under the atlas: exactly the two
`sstore`s. -/
theorem pushEvm_cached_sload {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) {v : UInt256}
    (s : UInt256) :
    (pushEvm σ (A.w2 + (l : UInt256)) v).sload s
      = ((σ.sstore (A.w2 + (l : UInt256))
            (σ.sload (A.w2 + (l : UInt256)) + 1)).sstore
          (A.wl l + σ.sload (A.w2 + (l : UInt256))) v).sload s := by
  rw [pushEvm_cached' hA hl]
  simp only [sload_mstore]

/-- **`padStep` under the atlas** (one pad-walk level: read `_zeros[l]`,
push it onto the level-`l` node array): two `sstore`s — the length bump at
`A.w2 + l` and the element write of `_zeros[l]` at `A.wl l + oldLen` —
followed by the three scratch `mstore 0`s. -/
theorem padStep_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) :
    padStep σ (l : UInt256)
      = ((((σ.sstore (A.w2 + (l : UInt256))
              (σ.sload (A.w2 + (l : UInt256)) + 1)).sstore
            (A.wl l + σ.sload (A.w2 + (l : UInt256)))
            (σ.sload (A.wz + (l : UInt256)))).mstore 0 2).mstore 0
              3).mstore 0 (A.w2 + (l : UInt256)) := by
  have h2f : (arrOut σ 2).1 = A.w2 := by rw [arrOut_cached_2 hA]
  have h2s : (arrOut σ 2).2 = σ.mstore 0 2 := by rw [arrOut_cached_2 hA]
  have h23 : arrOut (σ.mstore 0 2) 3 = (A.wz, (σ.mstore 0 2).mstore 0 3) :=
    arrOut_of_atlas_entry ((atlas_mstore0 2 hA).2.1)
  have h23f : (arrOut (σ.mstore 0 2) 3).1 = A.wz := by rw [h23]
  have h23s : (arrOut (σ.mstore 0 2) 3).2 = (σ.mstore 0 2).mstore 0 3 := by
    rw [h23]
  unfold padStep
  rw [h2s, h2f, h23s, h23f]
  rw [pushEvm_cached (atlas_mstore0 3 (atlas_mstore0 2 hA)) hl]
  simp only [sload_mstore, sstore_mstore_comm]

/-- Storage projection of `padStep` under the atlas. -/
theorem padStep_cached_sload {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) (s : UInt256) :
    (padStep σ (l : UInt256)).sload s
      = ((σ.sstore (A.w2 + (l : UInt256))
            (σ.sload (A.w2 + (l : UInt256)) + 1)).sstore
          (A.wl l + σ.sload (A.w2 + (l : UInt256)))
          (σ.sload (A.wz + (l : UInt256)))).sload s := by
  rw [padStep_cached hA hl]
  simp only [sload_mstore]

/-- **Root readback** (`fun_root`'s storage chain): reading element 0 of
the level-`H` array under the atlas is the sload at `rootSlot A H`. -/
theorem rootRead_cached {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) :
    (sibRead σ 2 (H : UInt256) 0).1 = σ.sload (rootSlot A H) := by
  rw [sibRead_cached hA (le_refl H) 0]
  show σ.sload (A.wl H + 0) = σ.sload (A.wl H)
  rw [add_zero]

/-! ## R1 — slot separations

All success witnesses come from the cache (`keccak_of_atlas_entry`); the
interval disagreements come from the word-0 readback
(`arrInterval_ne_of_slot_ne`).  Bound discipline: element indices and the
tree height are `< lowSlotBound = 2^32`. -/

/-- General two-sided keccak offset separation (local copy of the
`imt_fidelity_user` private): hashes of distinct preimages stay distinct
under any two small offsets. -/
private lemma keccak_off_ne_off
    {σ₁ σ₂ σ₁' σ₂' : EVMState} {p₁ n₁ p₂ n₂ r₁ r₂ k₁ k₂ : UInt256}
    (hk1 : σ₁.keccak256 p₁ n₁ = some (r₁, σ₁'))
    (hk2 : σ₂.keccak256 p₂ n₂ = some (r₂, σ₂'))
    (hne : mkInterval σ₁.machine_state p₁ n₁ ≠ mkInterval σ₂.machine_state p₂ n₂)
    (hs₁ : k₁.val < lowSlotBound)
    (hs₂ : k₂.val < lowSlotBound) :
    r₁ + k₁ ≠ r₂ + k₂ := by
  rcases Nat.le_total k₁.val k₂.val with hle | hle
  all_goals intro heq
  · have hd : ((k₂.val - k₁.val : ℕ) : UInt256).val = k₂.val - k₁.val := by
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
    exact keccak256_slot_sep hk2 hk1 (Ne.symm hne)
      (by rw [hd]; exact lt_of_le_of_lt (Nat.sub_le _ _) hs₂) hcore.symm
  · have hd : ((k₁.val - k₂.val : ℕ) : UInt256).val = k₁.val - k₂.val := by
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
    exact keccak256_slot_sep hk1 hk2 hne
      (by rw [hd]; exact lt_of_le_of_lt (Nat.sub_le _ _) hs₁) hcore

/-- **Cross-level element separation**: elements of DISTINCT levels never
collide, at any pair of small offsets. -/
theorem wl_off_ne_wl_off {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (hH : H < lowSlotBound)
    {l l' : ℕ} (hl : l ≤ H) (hl' : l' ≤ H) (hll' : l ≠ l')
    {j j' : UInt256} (hj : j.val < lowSlotBound)
    (hj' : j'.val < lowSlotBound) :
    A.wl l + j ≠ A.wl l' + j' := by
  have hH2 : H < 2 ^ 32 := hH
  have hlv : ((l : UInt256)).val = l := level_cast_val hl hH2
  have hlv' : ((l' : UInt256)).val = l' := level_cast_val hl' hH2
  have hcast : (l : UInt256) ≠ (l' : UInt256) := by
    intro h
    apply hll'
    have hval := congrArg Fin.val h
    rw [hlv, hlv'] at hval
    exact hval
  exact keccak_off_ne_off
    (keccak_of_atlas_entry (hA.2.2 l hl))
    (keccak_of_atlas_entry (hA.2.2 l' hl'))
    (arrInterval_ne_of_slot_ne (base_offset_ne hcast)) hj hj'

/-- **In-level element separation**: distinct offsets over one level base
(plain group arithmetic; no atlas needed). -/
theorem wl_off_ne_same_level {A : NodeAtlas} {l : ℕ} {j j' : UInt256}
    (h : j ≠ j') : A.wl l + j ≠ A.wl l + j' :=
  base_offset_ne h

/-- A level data base avoids every reserved low slot. -/
theorem wl_ne_low {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) (c : UInt256)
    (hc : c.val < lowSlotBound) :
    A.wl l ≠ c :=
  keccak256_ne_lowSlot c (keccak_of_atlas_entry (hA.2.2 l hl)) hc

/-- **Element vs low slots**: a node element never hits a reserved low
slot (count, height, lengths, …). -/
theorem wl_off_ne_low {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H) (j c : UInt256)
    (hj : j.val < lowSlotBound) (hc : c.val < lowSlotBound) :
    A.wl l + j ≠ c :=
  keccak256_add_ne_lowSlot j c (keccak_of_atlas_entry (hA.2.2 l hl)) hj hc

/-- A level header (`A.w2 + k`) never hits a reserved low slot. -/
theorem w2_off_ne_low {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (k c : UInt256)
    (hk : k.val < lowSlotBound) (hc : c.val < lowSlotBound) :
    A.w2 + k ≠ c :=
  keccak256_add_ne_lowSlot k c (keccak_of_atlas_entry hA.1) hk hc

/-- A `_zeros` element (`A.wz + k`) never hits a reserved low slot. -/
theorem wz_off_ne_low {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (k c : UInt256)
    (hk : k.val < lowSlotBound) (hc : c.val < lowSlotBound) :
    A.wz + k ≠ c :=
  keccak256_add_ne_lowSlot k c (keccak_of_atlas_entry hA.2.1) hk hc

/-- **Element vs header families**: a node element never hits an inner
header slot (`_nodes` outer data): the preimages differ at word 0
(`A.w2 + l` vs `2` — separated by `w2_off_ne_low`). -/
theorem wl_off_ne_w2_off {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (hH : H < lowSlotBound)
    {l : ℕ} (hl : l ≤ H) {j k : UInt256}
    (hj : j.val < lowSlotBound) (hk : k.val < lowSlotBound) :
    A.wl l + j ≠ A.w2 + k := by
  have hH2 : H < 2 ^ 32 := hH
  have hlv : ((l : UInt256)).val = l := level_cast_val hl hH2
  have hslot : A.w2 + (l : UInt256) ≠ (2 : UInt256) :=
    w2_off_ne_low hA (l : UInt256) 2
      (by rw [hlv]; exact lt_of_le_of_lt hl hH) (by decide)
  exact keccak_off_ne_off
    (keccak_of_atlas_entry (hA.2.2 l hl))
    (keccak_of_atlas_entry hA.1)
    (arrInterval_ne_of_slot_ne hslot) hj hk

/-- **Element vs `_zeros` family**: a node element never hits a `_zeros`
element (word-0 disagreement `A.w2 + l` vs `3`). -/
theorem wl_off_ne_wz_off {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) (hH : H < lowSlotBound)
    {l : ℕ} (hl : l ≤ H) {j k : UInt256}
    (hj : j.val < lowSlotBound) (hk : k.val < lowSlotBound) :
    A.wl l + j ≠ A.wz + k := by
  have hH2 : H < 2 ^ 32 := hH
  have hlv : ((l : UInt256)).val = l := level_cast_val hl hH2
  have hslot : A.w2 + (l : UInt256) ≠ (3 : UInt256) :=
    w2_off_ne_low hA (l : UInt256) 3
      (by rw [hlv]; exact lt_of_le_of_lt hl hH) (by decide)
  exact keccak_off_ne_off
    (keccak_of_atlas_entry (hA.2.2 l hl))
    (keccak_of_atlas_entry hA.2.1)
    (arrInterval_ne_of_slot_ne hslot) hj hk

/-- **Header vs `_zeros` family**: a level header never hits a `_zeros`
element (word-0 disagreement `2` vs `3`). -/
theorem w2_off_ne_wz_off {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {k k' : UInt256}
    (hk : k.val < lowSlotBound) (hk' : k'.val < lowSlotBound) :
    A.w2 + k ≠ A.wz + k' :=
  keccak_off_ne_off
    (keccak_of_atlas_entry hA.1)
    (keccak_of_atlas_entry hA.2.1)
    (arrInterval_ne_of_slot_ne (by decide : (2 : UInt256) ≠ 3)) hk hk'

/-! ## R2 start — atlas threading through walk primitives

The atlas survives EVERY walk primitive except the pair hash itself (the
`mstore 32` boundary): each of the following is scratch `mstore 0`s +
keccak steps + `sstore`s, all covered by the transports above — with NO
hit hypotheses (the atlas even survives fresh keccak draws). -/

/-- The atlas survives a `sibRead`. -/
theorem atlas_sibRead {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (b lvl j : UInt256) (hA : AtlasCachedAt σ A H) :
    AtlasCachedAt (sibRead σ b lvl j).2 A H := by
  show AtlasCachedAt (arrOut (arrOut σ b).2 ((arrOut σ b).1 + lvl)).2 A H
  exact atlas_arrOut _ (atlas_arrOut _ hA)

/-- The atlas survives a `sideRead`. -/
theorem atlas_sideRead {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (slot lvl : UInt256) (hA : AtlasCachedAt σ A H) :
    AtlasCachedAt (sideRead σ slot lvl).2 A H := by
  show AtlasCachedAt (arrOut σ slot).2 A H
  exact atlas_arrOut _ hA

/-- The atlas survives a `nodeStore` (any base/level, hit or fresh). -/
theorem atlas_nodeStore {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (base lvl j v : UInt256) (hA : AtlasCachedAt σ A H) :
    AtlasCachedAt (nodeStore σ base lvl j v) A H := by
  unfold nodeStore
  exact atlas_sstore _ _ (atlas_arrOut _ (atlas_arrOut _ hA))

/-- The atlas survives a `pushEvm`. -/
theorem atlas_pushEvm {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (arr v : UInt256) (hA : AtlasCachedAt σ A H) :
    AtlasCachedAt (pushEvm σ arr v) A H := by
  unfold pushEvm
  exact atlas_sstore _ _ (atlas_arrOut _ (atlas_sstore _ _ hA))

/-- The atlas survives a `leafWriteEvm` (any `ss`). -/
theorem atlas_leafWrite {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (ss idx leaf : UInt256) (hA : AtlasCachedAt σ A H) :
    AtlasCachedAt (leafWriteEvm σ ss idx leaf) A H := by
  unfold leafWriteEvm
  exact atlas_sstore _ _ (atlas_arrOut _ (atlas_arrOut _ hA))

/-- The atlas survives a `padStep`. -/
theorem atlas_padStep {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (i : UInt256) (hA : AtlasCachedAt σ A H) :
    AtlasCachedAt (padStep σ i) A H := by
  unfold padStep
  exact atlas_pushEvm _ _ (atlas_arrOut _ (atlas_arrOut _ hA))

/-! ### The pair-hash boundary: `CachedPair` and the hash-regime anchor

A pair hash (`accOut a b` = `mstore 0 a; mstore 32 b; keccak`) crosses
the anchor boundary: after it, the atlas junk `[32, 62]` is pinned by the
stored accumulator `b` (`arrInterval_mstore32_pinned`), so the atlas
entries needed for the SUBSEQUENT `arrOut`s live at `b`-regime intervals.
`AtlasCachedAtH σ A H b` names that pack state-independently (any
`(_.mstore 0 _).mstore 32 b` state carries the same intervals); in the
history induction it is discharged by `walk_caches` + monotonicity. -/

/-- The pair-hash cache certificate (blueprint §1.4): the `accOut`
preimage of `(a, b)` at anchor `σ` is cached to `r`. -/
def CachedPair (σ : EVMState) (a b r : UInt256) : Prop :=
  Finmap.lookup (accInterval σ a b) σ.keccak_map = some r

/-- The `b`-regime atlas pack: the atlas entries keyed at the post-hash
junk regime (junk `[32, 62]` = bytes of `b`), over `σ`'s cache. -/
def AtlasCachedAtH (σ : EVMState) (A : NodeAtlas) (H : ℕ) (b : UInt256) : Prop :=
  AtlasCachedAt ((σ.mstore 0 0).mstore 32 b) A H

/-- **RECONSTRUCTED 2026-08-11.**  `atlasH_at_hash_state` below called `byte_mstore32_pinned`, a
helper that no longer exists anywhere in the corpus — the dangling reference that stopped this file
compiling.  Its required statement is fixed by the use site: bytes `[32, 62]` lie inside the window
written by `mstore 32 b`, so they are a pure function of `b` and the offset, independent of the
underlying state and of whatever was stored at word 0.

That is exactly `KeccakDeterminism.lookup_updateMemory_at`'s content at the outer write, so the
reconstruction needs no new reasoning — only the index bookkeeping to present `i` as `(i - 32) + 32`. -/
theorem byte_mstore32_pinned {σ₁ σ₂ : EVMState} {y₁ y₂ b i : UInt256}
    (h32 : 32 ≤ i.val) (h62 : i.val ≤ 62) :
    Finmap.lookup i ((σ₁.mstore 0 y₁).mstore 32 b).machine_state.memory
      = Finmap.lookup i ((σ₂.mstore 0 y₂).mstore 32 b).machine_state.memory := by
  have hk : i.val - 32 < 32 := by omega
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have hkv : ((((i.val - 32 : ℕ)) : UInt256)).val = i.val - 32 :=
    Fin.val_cast_of_lt (by have := i.isLt; omega)
  have hi : i = (((i.val - 32 : ℕ)) : UInt256) + 32 := by
    apply Fin.ext
    show i.val = ((((i.val - 32 : ℕ)) : UInt256).val + ((32 : UInt256)).val) % UInt256.size
    rw [hkv, h32v, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    omega
  have hms₁ : ((σ₁.mstore 0 y₁).mstore 32 b).machine_state
      = (σ₁.machine_state.updateMemory 0 y₁).updateMemory 32 b := rfl
  have hms₂ : ((σ₂.mstore 0 y₂).mstore 32 b).machine_state
      = (σ₂.machine_state.updateMemory 0 y₂).updateMemory 32 b := rfl
  rw [hi, hms₁, hms₂,
      Clear.KeccakDeterminism.lookup_updateMemory_at _ 32 b _ hk
        Clear.KeccakDeterminism.window_32_nodup,
      Clear.KeccakDeterminism.lookup_updateMemory_at _ 32 b _ hk
        Clear.KeccakDeterminism.window_32_nodup]

/-- The `b`-regime pack applies at ANY concrete post-hash state that
stores `b` at word 32 and carries `σ`'s cache. -/
theorem atlasH_at_hash_state {σ Y : EVMState} {A : NodeAtlas} {H : ℕ}
    {y b : UInt256}
    (hmap : Y.keccak_map = σ.keccak_map)
    (hAh : AtlasCachedAtH σ A H b) :
    AtlasCachedAt ((Y.mstore 0 y).mstore 32 b) A H := by
  refine atlas_of_junk_agree ?_ ?_ hAh
  · intro i h32 h62
    exact byte_mstore32_pinned h32 h62
  · intro I w h
    show Finmap.lookup I Y.keccak_map = some w
    rw [hmap]
    exact h

/-- High-byte frame through a scratch `mstore 0` (for the pair-hash junk
window `[64, 95)`). -/
private lemma lookup_mstore0_high {σ : EVMState} {b i : UInt256}
    (hi : 32 ≤ i.val) :
    Finmap.lookup i (σ.mstore 0 b).machine_state.memory
      = Finmap.lookup i σ.machine_state.memory := by
  show Finmap.lookup i (σ.machine_state.updateMemory 0 b).memory
      = Finmap.lookup i σ.machine_state.memory
  rw [lookup_updateMemory_outside_val σ.machine_state 0 b i
      (by rw [val_0]; norm_num) (Or.inr (by rw [val_0]; omega))]

/-- **The odd-branch walk level under the atlas + a pair-hash HIT**
(WalkAtlasOK, odd case): the sibling read is the atlas `sload`, the pair
hash returns the cached `r` with memory effect `mstore 0/32` only, and
the level output is `r` stored at the parent slot of the hash-regime
scratch state. -/
theorem stepOdd_hit {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H)
    {idx cur r : UInt256}
    (hpair : CachedPair σ (σ.sload (A.wl l + (idx - 1))) cur r) :
    stepOdd σ 2 (l : UInt256) idx cur
      = (r, nodeStore
          ((((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).mstore 0
              (σ.sload (A.wl l + (idx - 1)))).mstore 32 cur)
          2 ((l : UInt256) + 1) (Fin.shiftRight idx 1) r) := by
  have hsib := sibRead_cached hA hl (idx - 1)
  have hsibf : (sibRead σ 2 (l : UInt256) (idx - 1)).1
      = σ.sload (A.wl l + (idx - 1)) := by rw [hsib]
  have hsibs : (sibRead σ 2 (l : UInt256) (idx - 1)).2
      = (σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256)) := by rw [hsib]
  have hjunk : ∀ i : UInt256, 64 ≤ i.val → i.val ≤ 94 →
      Finmap.lookup i σ.machine_state.memory
        = Finmap.lookup i
            ((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).machine_state.memory := by
    intro i hi _
    rw [lookup_mstore0_high (by omega), lookup_mstore0_high (by omega)]
  have hacc : accOut ((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256)))
        (σ.sload (A.wl l + (idx - 1))) cur
      = (r, (((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).mstore 0
              (σ.sload (A.wl l + (idx - 1)))).mstore 32 cur) :=
    accOut_of_cached_frame hjunk hpair
  have haccf : (accOut ((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256)))
        (σ.sload (A.wl l + (idx - 1))) cur).1 = r := by rw [hacc]
  have haccs : (accOut ((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256)))
        (σ.sload (A.wl l + (idx - 1))) cur).2
      = (((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).mstore 0
          (σ.sload (A.wl l + (idx - 1)))).mstore 32 cur := by rw [hacc]
  unfold stepOdd
  rw [hsibs, hsibf, haccf, haccs]

/-- Value projection of the odd hit level: the accumulator becomes the
cached pair hash. -/
theorem stepOdd_hit_fst {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H)
    {idx cur r : UInt256}
    (hpair : CachedPair σ (σ.sload (A.wl l + (idx - 1))) cur r) :
    (stepOdd σ 2 (l : UInt256) idx cur).1 = r := by
  rw [stepOdd_hit hA hl hpair]

/-- **WalkAtlasOK (odd case)**: given the level-entry atlas, the pair-hash
hit, and the `cur`-regime pack, the atlas holds again at the level exit —
the next level's reads hit the cache. -/
theorem stepOdd_hit_atlas {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl : l ≤ H)
    {idx cur r : UInt256}
    (hpair : CachedPair σ (σ.sload (A.wl l + (idx - 1))) cur r)
    (hAh : AtlasCachedAtH σ A H cur) :
    AtlasCachedAt (stepOdd σ 2 (l : UInt256) idx cur).2 A H := by
  rw [stepOdd_hit hA hl hpair]
  show AtlasCachedAt (nodeStore
      ((((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).mstore 0
          (σ.sload (A.wl l + (idx - 1)))).mstore 32 cur)
      2 ((l : UInt256) + 1) (Fin.shiftRight idx 1) r) A H
  exact atlas_nodeStore _ _ _ _ (atlasH_at_hash_state rfl hAh)

/-- Storage projection of the odd hit level: exactly one `sstore` of the
cached hash at the parent element slot. -/
theorem stepOdd_hit_sload {σ : EVMState} {A : NodeAtlas} {H : ℕ}
    (hA : AtlasCachedAt σ A H) {l : ℕ} (hl1 : l + 1 ≤ H)
    {idx cur r : UInt256}
    (hpair : CachedPair σ (σ.sload (A.wl l + (idx - 1))) cur r)
    (hAh : AtlasCachedAtH σ A H cur) (s : UInt256) :
    (stepOdd σ 2 (l : UInt256) idx cur).2.sload s
      = (σ.sstore (A.wl (l + 1) + Fin.shiftRight idx 1) r).sload s := by
  have hl : l ≤ H := le_trans (Nat.le_succ l) hl1
  rw [stepOdd_hit hA hl hpair]
  show (nodeStore
      ((((σ.mstore 0 2).mstore 0 (A.w2 + (l : UInt256))).mstore 0
          (σ.sload (A.wl l + (idx - 1)))).mstore 32 cur)
      2 ((l : UInt256) + 1) (Fin.shiftRight idx 1) r).sload s
    = (σ.sstore (A.wl (l + 1) + Fin.shiftRight idx 1) r).sload s
  rw [← Nat.cast_add_one]
  rw [nodeStore_cached_sload (atlasH_at_hash_state rfl hAh) hl1]
  simp only [sstore_mstore_comm, sload_mstore]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
