# ROOT-FIDELITY BLUEPRINT — the IMT node arrays and root realize the Merkle hash of the leaf set

Recon 2026-07-23 (subagent, read-only sweep; all citations verified against source).
Status: PLANNED — next major track after the #67 weld. Leaf-set fidelity (#60–#66) is done;
this track proves the *stored node arrays and root* commit the whole leaf list.

## 0. Ground truth gathered (what exists, with citations)

### 0.1 Storage layout (consensus-critical, documented in source)

`_imt` sits at slot 0 (`era-contracts/l1-contracts/contracts/atomic-interop/L2InteropCommitmentTree.sol:27-33`; layout doc at lines 22-24: *"the bootloader … loads `_height` from slot 0 and derives the `_nodes[_height][0]` slot from the `_nodes` base slot 2"*). With `FullTree` = `{_height, _leafNumber, _nodes, _zeros}` (`era-contracts/l1-contracts/contracts/common/libraries/FullMerkle.sol:14-19`) and the `IMT` wrapper (`era-contracts/l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol:30-34`):

| slot | content | Lean shadow |
|---|---|---|
| 0 | `tree._height` (walk level count) | `sload 0` — loop bound in `update_loop` (`imt_update_fold_user.lean:925-936`) |
| 1 | `tree._leafNumber` (count) | `leafSetOf` range (`imt_fidelity_user.lean:96-97`) |
| 2 | `tree._nodes : bytes32[][]` — outer length; outer data at `keccak(2)`; level-`l` inner header at `keccak(2)+l` (inner length); inner data at `keccak(keccak(2)+l)`, element `j` at `+j` | `arrOut`/`sibRead` (`imt_storage_atoms_user.lean:110-111, 616-619`) |
| 3 | `tree._zeros : bytes32[]` — length at 3, data at `keccak(3)+i` | `sideRead σ (ss+3) i` (`imt_storage_atoms_user.lean:771-772`) |
| 4 | `leaves` mapping — leaf `i` at `keccak(i‖4)` (fields `value/nextIndex/nextValue` at `+0/+1/+2`) | `leafSlot`/`decodeLeaf` (`imt_fidelity_user.lean:87-93`) |
| 5 | `valueToIndex` mapping | `vtiSlot` (`imt_fidelity_user.lean:838`) |

**Where the root lives / is read.** `FullMerkle.root` = `_nodes[_height][0]` (`FullMerkle.sol:99-101`). The compiled read `fun_root` (`yul/L2InteropCommitmentTree.yul:811-830`) is: `h := sload(0)`; guard `h < sload(2)`; `slot := keccak(2)+h`; guard `sload(slot) ≠ 0` (inner length nonzero); return `sload(keccak(slot))`. So **rootSlot σ = keccak(keccak(2) + sload 0) + 0** — element 0 of the level-`height` inner array. The insert arm never calls `fun_root`; it *returns and logs* `var_newRoot` (the walk output) directly (`yul/L2InteropCommitmentTree.yul:260-268`), while the bootloader reads the storage slot. So the capstone must be about **`sload(rootSlot)` of the final state**, with `var_newRoot = sload(rootSlot)` as a corollary.

### 0.2 The walk side (all closed forms already proven)

- Per-level step: `stepOdd`/`stepEven`/`stepEdge` (`imt_update_fold_user.lean:65-69, 297-301, 559-563`), dispatched by `updateStep` (`:818-821`), iterated by `updateWalk ss base k σ i idx maxN cur → (evm, i, idx, maxN, cur)` (`:824-831`). Recurrence per level `i` at index `idx`, frontier `maxN`:
  - `idx` odd: `sib := sibRead σ base i (idx−1)` (= `sload(keccak(keccak(base)+i) + (idx−1))`, two `arrOut` keccak steps); `cur' := accOut(sib, cur).1` = `H(sib‖cur)`;
  - `idx` even, `maxN ≠ idx`: `sib := sibRead σ base i (idx+1)`; `cur' := accOut(cur, sib).1`;
  - `idx` even, `maxN = idx` (frontier edge): `sib := sideRead σ (ss+3) i` = `sload(keccak(3)+i)` — **`_zeros[i]`, not a node duplicate**; `cur' := accOut(cur, sib).1`;
  - then `nodeStore base (i+1) (idx >>> 1) cur'` — `sstore` of the parent at level `i+1`, index `idx >>> 1` (`:59-61`); indices halve, `maxN` halves.
- Full-function closed forms: `updateLeaf_call` (`imt_update_fold_user.lean:1516-1537`; walk base `ss+2`, level count `sload ss`, `maxN = sload(ss+1) − 1`, leaf pre-write `leafWriteEvm` at level-0 element `idx`, `:1430-1432`); the `_5205` twins (`imt_update_5205_user.lean:1222, 1599, 1776`); `pushNewLeaf_call` non-growth (`imt_pad_user.lean:850-922`: count bump `sstore 1 (c+1)`, pad `padWalk` (`:353-357`, step pushes `_zeros[i]` onto `_nodes[i]` via `pushEvm`, `:51-53`, `imt_push_user.lean:174-176`), then delegate to the updateLeaf walk); growth branch separately as `grow_if`/`pushNewLeaf_call_grow` (`imt_pad_user.lean:1069-1170`).
- The whole glue: `insertGlue_prefix` (`imt_insert_gate_user.lean:2131-2279`) ends in evm `(pushOutW …).1` and `var_newRoot = (pushOutW …).2.2.2.2`; the stage abbreviations `updTreeW/insertUpdEvm/insertNewEvm/pushPadW/pushOutW` (`:1938-1965`) name exactly the states root fidelity must decode. Note `pushOutW`'s walk has `idx = old count = maxN` → the new leaf's right siblings come from the **edge branch (`_zeros`)** at every frontier level.
- Frames already proven: walks/pad preserve low slots (`updateWalk_sload_low`, `padWalk_sload_low`, `StepLowOK`, `PadLowOK` — `imt_walk_discharge_user.lean:206-236, 328-334`), the count (`updateWalk_sload_one`/`padWalk_sload_one`, `imt_fidelity_user.lean:1781-1793`), the leaf-slot family (`updateWalk_sload_leaf`/`padWalk_sload_leaf`/D-series, `imt_fidelity_user.lean:1405-1760`), and the junk window `[64,95)` (`updateWalk_junk` `imt_replay_user.lean:159`, `padWalk_junk` `imt_fidelity_user.lean:1624`).

### 0.3 Hash side

- Node hash: `accOut σ a b = keccakOut ((σ.mstore 0 a).mstore 32 b) 0 64` (`specs/KeccakDeterminism.lean:481-486`); `efficientHash_call_acc` (`imt_hash_user.lean:92`). Leaf hash: `hashLeafOut` — keccak of the 96-byte struct region at `P+32`, `P = mload 64` (`imt_hash_user.lean:325-335`), determinism under junk-tail + cache transport (`hashLeafOut_deterministic`, `:778-814`). **The leaf hash covers all three fields including `nextIndex`** (`IndexedMerkleTree.sol:123-125`), which `AbsLeaf`/`decodeLeaf` deliberately drop — root fidelity needs the 3-field decode (see §1).
- Pure fold target exists: `foldRoot` (`specs/AtomicFlowManager/AtomicFlowManager/imt_path_user.lean:551-557`), whole-function `calculateRootMemory_call` (`imt_path_toplevel_user.lean:47`), M1–M3 ledger entry #24 (`SECURITY_VERIFICATION.md:609-633`). And crucially the **walk↔fold replay is done**: `foldWalk`/`walkSib`/`walkHash`/`walkPreHash`/`walkPair` (`imt_agreement_user.lean:75-194`), `fold_walk_agree` (`:211`), `walk_caches` (`imt_replay_user.lean:314`), `fold_replays_walk` (`:391`), `root_pins_written_leaf` (`:462`), `foldRoot_binding` (`specs/AtomicFlowManager/AtomicFlowManager/merkle_binding_user.lean:176`). **What is missing is not path replay but the tree-shaped statement**: the stored node arrays are level-wise correct so that `sload(rootSlot)` commits *the whole leaf list*, not just the last-touched path.

### 0.4 Abstract side

`specs/IMTAbstract.lean`: `AbsLeaf` (`:35`), `GapSound/KeyInj` (`:42-47`), `imtInsert` (`:65-66`), `Evolution` (`:189-192`), invariants and the atomicity capstones (#60, `:919`). Nothing about roots, hashes, positions, or zero-padding exists there. The fidelity chain #61–#66 (`SECURITY_VERIFICATION.md:1355-1449`) ends at `glueSeq_leafSetOf` (`imt_fidelity_user.lean:1897-1960`) = the *leaf-set* equation over the composed chain σ₀→E4→S1→S2→F4→F5→S3→SB→SP→SW→SF (anchor diagram `:1795-1856`). Root fidelity is the same chain, read at the *node-array* slots instead of the leaf slots.

### 0.5 The model artifact that shapes everything (read this before estimating)

`mkInterval ms p n` = the list of **word reads** (`lookupMemory`) at byte addresses `p..p+n−1` (`Clear/Clear/EVMState.lean:208-212`); `keccak256` keys the cache on that list and draws *fresh* outputs from `keccak_range` steered by `used_range` (`:214-224`; `sstore` grows `used_range`). Consequences:
- `accInterval` (64-byte scratch) depends on junk bytes `[64,95)` — handled by the tri-anchor pack in #66 because only the two allocator bumps write there.
- **`arrOut`'s interval (`keccak(0,32)` after `mstore 0 a`) depends on bytes `[0,62]`, of which `[32,62]` are junk — and every `accOut` rewrites `[32,63]` (`mstore 32 b`).** So *each pair-hash step invalidates the array-slot interval*. Two computations of "keccak(2)" at different points of the walk are **different cache keys** and, on the fresh branch, return **different slot values**. The existing walk lemmas never needed slot agreement across levels (the walk reads siblings, never its own writes, and `PassOK` (`imt_update_fold_user.lean:883-913`) is stated over the step's own recomputation). Root fidelity, by contrast, is *all about* reading back what an earlier `arrOut`-addressed store wrote — at `sibRead` sites of walk #2, at the next insert, and at `fun_root`. This forces a **per-anchor array-slot cache pack** (the `arrOut` analog of #66's tri-anchor pack, but with one anchor per `accOut` occurrence, i.e. O(height) anchors per walk). This is the single biggest cost driver of the track.

---

## 1. Abstract definitions to add

### 1.1 Pure Merkle spec (new file `specs/MerkleSpec.lean` — EVM-free, mirrors `IMTAbstract`'s style)

```lean
variable (h : UInt256 → UInt256 → UInt256) (z0 : UInt256)

def zeros : ℕ → UInt256                       -- z 0 = z0; z (l+1) = h (z l) (z l)
def levelUp (z : UInt256) : List UInt256 → List UInt256
  -- pairwise h; a lone left tail x maps to h x z   (FullMerkle edge = right sibling _zeros[l])
def levels (leaves : List UInt256) : ℕ → List UInt256   -- iterate levelUp with zeros l
def rootOf (leaves : List UInt256) (height : ℕ) : UInt256 := (levels leaves height).headD (zeros height)
def walkPure (sibs : ℕ → UInt256) : ℕ → UInt256 → UInt256 → UInt256   -- the pure updateWalk: orient by parity, h, halve
```

Pure lemmas (no EVM, no axioms):
- **M-A `walkPure_update`**: if `sibs l` = the level-`l` sibling of `idx` in `levels leaves` (with `zeros l` beyond the frontier), then `walkPure sibs height idx x = rootOf (leaves.set idx x) height`, and each intermediate value equals `(levels (leaves.set idx x) (l+1)).get (idx >>> (l+1))`. This is the crux converting a one-path walk into whole-tree recomputation. Induction on `height`; the standard "sibling levels of `set idx` agree with sibling levels of `leaves`" helper.
- **M-B `rootOf_append`**: for `leaves.length < 2^height`, `rootOf (leaves ++ [x]) height` equals `walkPure sibs height leaves.length x` where the sibling stream is: node when inside the frontier, `zeros l` at the frontier edge — matching `stepEdge`'s `_zeros` read and the `padWalk` frontier extension.
- **M-C `levels_length`** (frontier arithmetic): `(levels leaves l).length = ⌈leaves.length / 2^l⌉`-style facts, `idx >>> height = 0` for `idx < 2^height` (bridges `Fin.shiftRight` vs `Nat` division — small but fiddly).
- **M-D `rootOf_inj_of_h_inj`** (optional, for the binding corollary): pointwise injectivity of `rootOf` given injective `h` on the used pairs — the tree-shaped generalization of `foldRoot_binding`.

`h` stays a **parameter**; it is instantiated per-theorem from the keccak cache (§2, R6). Do *not* try to define a global pure keccak — the model has none.

### 1.2 Three-field leaf decode (extends `imt_fidelity_user.lean`'s alphabet)

```lean
def decodeLeaf3 (σ : EVMState) (i : UInt256) : UInt256 × UInt256 × UInt256 :=
  (σ.sload (leafSlot σ i), σ.sload (leafSlot σ i + 1), σ.sload (leafSlot σ i + 2))
```
plus `leafHashes σ hl : List UInt256 := (range (sload 1).val).map hl` with a per-index leaf-hash oracle `hl` bound to the cache (below). `decodeLeaf3` reuses every `leafSlot` frame verbatim (the `+1` offset lemmas already exist: `leafSlot_add_ne`, `leafSlot_off_ne_off`, `imt_fidelity_user.lean:392-433`).

### 1.3 The slot atlas (new file `specs/L2InteropCommitmentTree/L2InteropCommitmentTree/imt_root_atlas_user.lean`)

```lean
def arrInterval (σ : EVMState) (a : UInt256) : List UInt256 :=
  mkInterval (σ.mstore 0 a).machine_state 0 32

structure NodeAtlas where
  w2 : UInt256                 -- keccak(2): outer _nodes data base; level-l inner header at w2 + l
  wl : ℕ → UInt256             -- keccak(w2 + l): level-l inner data base
  wz : UInt256                 -- keccak(3): _zeros data base

def AtlasCachedAt (σ : EVMState) (A : NodeAtlas) (H : ℕ) : Prop :=
  Finmap.lookup (arrInterval σ 2) σ.keccak_map = some A.w2
  ∧ Finmap.lookup (arrInterval σ 3) σ.keccak_map = some A.wz
  ∧ ∀ l ≤ H, Finmap.lookup (arrInterval ((σ.mstore 0 2)) (A.w2 + l)) σ.keccak_map = some (A.wl l)
  -- (exact scratch-state in the inner interval to be matched to sibRead's real chain)

def nodeAt (σ : EVMState) (A : NodeAtlas) (l : ℕ) (j : UInt256) := σ.sload (A.wl l + j)
def lenAt  (σ : EVMState) (A : NodeAtlas) (l : ℕ) := σ.sload (A.w2 + l)
def zeroAt (σ : EVMState) (A : NodeAtlas) (l : ℕ) := σ.sload (A.wz + l)
def rootSlot (A : NodeAtlas) (H : ℕ) := A.wl H     -- + 0
```

The atlas makes node addresses **state-independent names**, which is the only way to compare writes and reads separated by junk-window churn. `AtlasCachedAt` must be hypothesized (and re-derived) at every `arrOut` call site along the chain — see R1/R2.

### 1.4 Tree invariant + hash pack

```lean
def CachedPair (σ : EVMState) (a b r : UInt256) : Prop :=
  Finmap.lookup (accInterval σ a b) σ.keccak_map = some r     -- junk-stable via accInterval_eq

structure TreeShape (σ) (A) : Prop :=    -- pure arithmetic layout
  height small (< 2^32); count ≤ 2^height; sload 2 = height + 1; zeros length = height + 1;
  lenAt σ A l = frontier width at level l  (M-C arithmetic)

def TreeHash (σ) (A) (h) : Prop :=       -- every stored parent is the h-image of its children
  (∀ l < height, ∀ j < lenAt σ A (l+1),
     nodeAt σ A (l+1) j = h (child l (2j)) (child l (2j+1 or zeroAt σ A l))
     ∧ CachedPair σ (children…) (nodeAt σ A (l+1) j))
  ∧ zeros chain: zeroAt σ A (l+1) = h (zeroAt σ A l) (zeroAt σ A l) ∧ cached
  ∧ level 0: nodeAt σ A 0 m = hl m (the leaf-hash oracle), CachedLeaf-backed
```

The `CachedPair` conjuncts are what make the *next* insert's sibling reads and the `h`-instantiation work; they are the concrete shadow of "keccak is a function", exactly as the #66 pack was for `accOut _ 4` (`imt_fidelity_user.lean:1827-1834`).

---

## 2. Ordered lemma stack (bottom → capstone)

**R0 — `arrInterval` transport kit** (atlas file). (i) `arrInterval` is `sstore`-invariant (uses `machine_state_sstore'`, `imt_fidelity_user.lean:58`); (ii) invariant under `mstore` at addresses ≥ 64 (allocator bumps) and at 0 (self-overwrite by the next `arrOut`) — byte-window arithmetic like `accessor_interval_eq` (`KeccakDeterminism.lean:453-473`) but for `[0,62]`; (iii) **changed by `mstore 32`** — no lemma, this is the anchor boundary. Effort: S–M. Direct model reasoning; all byte-fold helpers exist (`lookup_updateMemory_outside_val`, `byte_double_mstore_eq`).

**R1 — cached-hit atlas reads.** Under `AtlasCachedAt σ A H`: `arrOut σ 2 = (A.w2, σ.mstore 0 2)` (via `keccakOut_of_cached`, `KeccakDeterminism.lean:216`); `sibRead σ 2 l j = (nodeAt σ A l j, …)`; `sideRead σ 3 l = zeroAt σ A l`; `nodeStore σ 2 l j v = σ.sstore (A.wl l + j) v` up to the two now-trivial `mstore 0` scratches; `leafWriteEvm σ 0 idx x` = `sstore (A.wl 0 + idx) x`; `pushEvm` = length bump at `A.w2 + l` + write at `A.wl l + len`; **`rootSlot` readback**: a new lemma `fun_root`-shaped `rootRead σ A = sload (A.wl H)` (and, if wanted, a closed form of `fun_root` itself — the Yul at `yul/L2InteropCommitmentTree.yul:811-830` is 8 statements, easy given R1). Effort: M (mechanical once R0 fixes the exact interval expressions; the subtlety is matching the *actual* scratch state in `sibRead`'s second `arrOut` — its interval junk `[32,62]` is inherited from the step's preceding `accOut`, so `AtlasCachedAt` must be stated over precisely that state; expect one iteration to get the definition right).

**R2 — atlas threading through one walk level** (`WalkAtlasOK`, the `PassOK` twin). Given `AtlasCachedAt` at the level entry + the level's `CachedPair` (so `accOut` is a cache **hit**, `accOut_of_cached` `KeccakDeterminism.lean:524` — no fresh draw, no `used_range` movement, memory effect = two `mstore`s), derive `AtlasCachedAt` at the next level entry: the only memory write between anchors is the hit-`accOut`'s `mstore 0/32`, and R0(i,ii) carries the entries across the `sstore`s. **Key simplification: with the pair hashes pre-cached, the walk performs *zero* fresh keccaks, so one atlas pack at walk entry suffices** — the O(height) anchor explosion collapses. This is the design decision to take: state the walk-level theorems over *pre-cached* pair hashes (the caller pack supplies them), not over fresh-drawing walks. `walk_caches` (`imt_replay_user.lean:314`) shows the fresh-drawing walk caches exactly these pairs, so for the *history* induction the pack for insert n+1 is discharged by insert n's `walk_caches` + monotonicity (`updateWalk_lookup_mono` `imt_agreement_user.lean:167`, `padWalk_lookup_mono` `imt_fidelity_user.lean:1667`) + junk re-anchoring (`accInterval_eq`). Effort: L. This is the heart of the file.

**R3 — walk node-content theorem** (`updateWalk_nodes`). Under `TreeShape`, atlas + pair pack, and the existing `StepLowOK`/`PassOK` bounds: after `updateWalk … k (leafWrite base state) 0 idx maxN x`,
`nodeAt SF A l j = if j = idx >>> l then pure-path value else nodeAt σ₀ A l j` for all `l ≤ k`, the final `cur = walkPure h sibs k idx x` with `sibs l = nodeAt σ₀ A l (sibling)` or `zeroAt` at the edge, and every touched parent is `CachedPair`-certified. Induction over `updateWalk` exactly like D3 (`updateWalk_sload_leaf`, `imt_fidelity_user.lean:1533`) but keeping the *written* slots as content, not just frames. Node-slot-vs-node-slot separation inside one level family: `A.wl l + j ≠ A.wl l' + j'` for `l ≠ l'` via `keccak_off_ne_off` (`imt_fidelity_user.lean:521-566`) with word-0 interval disagreement (`mkInterval_0_64_ne_of_word0_ne` analog at length 32 — trivial: byte-0 word is pinned by `mstore 0`); same-level distinct `j` is plain `Fin` arithmetic (`base_offset_ne`, `imt_leaf_storage_user.lean:897`). Effort: L (the biggest single proof, but every technique is a rehearsed pattern from D3/`update_loop`).

**R4 — pad node-content theorem** (`padWalk_nodes`): `lenAt` grows by one exactly on levels where `om ≠ m`, appended element = `zeroAt σ A l`, nothing else moves; plus M-C arithmetic showing this extends the frontier so walk #2's `PassOK`/edge dispatch matches M-B's sibling stream. Effort: M.

**R5 — leaf-write/leaves-side ↔ node-side mutual frames.** The mirror of D-series: the S1/F5 struct copies (64-byte-preimage slots), the vti write, and the count bump all miss every `A.wl l + j` and `A.w2 + l`, `A.wz + l` — `keccak_off_ne_off` with 64-vs-32 `mkInterval_ne_of_len_ne` (`KeccakInjective.lean:317`) in the *opposite orientation* from `arr_elem_ne_leafSlot_add` (`imt_fidelity_user.lean:570-583`), plus `keccak256_add_ne_lowSlot` for slots 0–3. Result: `nodeAt`/`lenAt`/`zeroAt` are invariant across the retarget copy, new-leaf copy, vti write; and `TreeHash`'s `CachedPair` entries survive (cache untouched by `sstore`, intervals re-anchored across the two allocator bumps via `accInterval_eq` — the same tri-anchor discipline as #66). Effort: M.

**R6 — the `h`-instantiation lemma.** Given the final state's cache (walks only grow it), define `h := fun a b => ((SF.keccak_map.lookup (accInterval SF a b)).getD 0)` — or keep `h` universally quantified with `CachedPair`-agreement hypotheses (recommended: matches house style; a `choose`-based corollary can package it). Show every `CachedPair σ_i a b r` along the chain yields `h a b = r` (cache monotonicity + `accInterval_eq` junk re-anchoring). Effort: S–M.

**R7 — phase composition over `glueSeq`** (`glueSeq_nodes`, the root twin of `glueSeq_leafSetOf`). Over the *identical* state chain σ₀…SF (`imt_fidelity_user.lean:1903-1922`):
`levels`-content after SF = `levels (leafHashes')` where `leafHashes' = (leafHashes σ₀).set IX hL' ++ [hL_new]`, by M-A (walk #1 at `IX`), R5 (staging frames), R4 + M-B (pad + walk #2 at `count`), and `TreeShape SF` restored. Effort: L (assembly; every ingredient from R3–R5, mirrors the existing 450-line capstone at `imt_fidelity_user.lean:1897`).

**R8 — CAPSTONE `rootFidelity_insert`.** Under `insertGlue_prefix`'s hypotheses + the packs:
```
sload_(SF) (rootSlot A height) = MerkleSpec.rootOf h (zeroAt σ₀ A 0) (leafHashes SF) height
∧ var_newRoot = that value
∧ TreeShape SF ∧ TreeHash SF (invariant re-established)
```
with `leafHashes SF` pinned to the abstract insert by #66: index `IX` ↦ hash of the retargeted `⟨k_w, NI, V⟩`, index `count` ↦ hash of `⟨V, oldNextIndex, W₀.nextKey⟩`, others unchanged — i.e. **`sload(rootSlot)` commits `imtInsert (leafSetOf σ₀) (decodeLeaf σ₀ IX) V`** through the leaf-hash layer. Root readback = R1's `rootRead` + "the walk's last store is the root": final `nodeStore` lands at level `height`, index `idx >>> height = 0` (M-C, needs `count < 2^height` from `TreeShape`; note `hnp` in `pushNewLeaf_call` only excludes *equality* — the strict bound is TreeShape's job), and no later write touches it. Effort: M given R7.

**R9 — history induction + verifier hookup** (optional but cheap): `Evolution`-style induction re-establishing `TreeShape ∧ TreeHash` from genesis (`initL2`/`setup` seeds `_zeros=[zₗ]`, `_nodes=[[zₗ]]`, leaf 0 — `IndexedMerkleTree.sol:42-51`; no generated closed form exists for the `initL2` dispatcher arm — either quote it source-verbatim like #63 or take genesis as hypothesis). Then compose with `fold_replays_walk`/`root_pins_written_leaf` and M-D to upgrade #25/#26's gates: *any* accepted inclusion/exclusion proof against a published root speaks about the `imtInsert`-evolved leaf set — closing the loop to #60. Effort: M.

Suggested file layout: `MerkleSpec.lean` (M-A…M-D), `imt_root_atlas_user.lean` (R0–R2), `imt_root_walk_user.lean` (R3–R5), `imt_root_user.lean` (R6–R9).

---

## 3. Difficulty notes and helper transfer (summary table)

| Item | Effort | Transfers directly |
|---|---|---|
| M-A/M-B/M-C | M/M/S | pure; `foldWalk_foldRoot` induction style (`imt_agreement_user.lean:89-105`) |
| R0 | S–M | `machine_state_sstore'`, byte-fold kit (`KeccakDeterminism.lean:236-341, 857-1011`) |
| R1 | M | `keccakOut_of_cached/accOut_of_cached`, `sload_arrOut_of_clean` family (`imt_walk_discharge_user.lean:34-83`) |
| R2 | **L** | `walk_caches`, `updateWalk_lookup_mono`, `accInterval_eq`, `updateWalk_junk` |
| R3 | **L** | D-series induction skeleton (`imt_fidelity_user.lean:1405-1583`), `PassOK` threading, `keccak_off_ne_off` |
| R4 | M | `pad_loop`, `pushEvm`, `padWalk_sload_low` |
| R5 | M | `arr_elem_ne_leafSlot_add` reversed, tri-anchor discipline verbatim from #66 |
| R6 | S–M | cache monotonicity lemmas |
| R7 | L | `glueSeq_leafSetOf` as the structural template (same state chain, same anchors) |
| R8 | M | `insertGlue_prefix` stage abbreviations; `updateWalk_sload_one` pattern for "no later clobber" |
| R9 | M | `evolution_invariant` pattern; #63's source-verbatim quoting for `initL2` |

---

## 4. Honest open modeling questions

1. **`arrOut` cache-key churn (the decisive artifact).** `arrInterval` depends on junk bytes `[32,62]`, rewritten by every `accOut` (`mstore 32`). The blueprint's answer — pre-cached pair hashes make the walk keccak-free, so one atlas anchor per phase suffices (R2) — must be validated on the *first* walk of a fresh history, where pair hashes are genuinely fresh draws. There the walk itself is fresh-drawing and the atlas entries must be re-anchored per level after each fresh `accOut` (its memory effect is still just `mstore 0/32`, so R0 covers it — but `AtlasCachedAt`'s inner-interval expression must be junk-parametric). Risk: the definition of `AtlasCachedAt` may need one redesign iteration.
2. **Freshness vs. existing slot values.** A fresh keccak draw is only constrained by the axioms (`keccak256_inj/slot_sep/ne_lowSlot/add_ne_lowSlot`, `KeccakInjective.lean:38, 280-300`) against *other keccak calls* and low slots. `TreeHash`'s `CachedPair` certificates deliberately avoid needing more; check no step needs "fresh output ∉ {arbitrary stored values}", which the trusted base does not provide.
3. **Growth branch.** `insertGlue_prefix` covers the non-growth path (`hnp`); inserts crossing `count = 2^height` take `grow_if` (`imt_pad_user.lean:1090`, `pushNewLeaf_call_grow` `:1170`) — new `_zeros` entry `H(z,z)` + new `_nodes` level. `TreeShape/TreeHash` were designed to extend (zeros chain is part of the invariant), but the glue-level composition for the growth arm is extra work not counted above. Decide scope up front.
4. **Genesis.** No generated Lean for the `initL2` arm (dispatcher glue, like the insert arm before #63/#65). Options: source-verbatim quotation, or `TreeShape ∧ TreeHash` at genesis as a Part-A-style assumption.
5. **`AbsLeaf` has no `nextIndex`, but the leaf hash does.** Root fidelity must either thread `decodeLeaf3` (recommended, §1.2) or add an index-aware abstract layer. The #66 statement pins `nextIndex` values implicitly (`NI`/`NI4` appear in `glueSeq_leafSetOf`'s chain) — the read-backs needed for `decodeLeaf3` agreement are already in `newLeafStage_decode`/`retargetStage_decode` (`imt_fidelity_user.lean:956, 1115`).
6. **Leaf-hash anchor set.** The two `hashLeafOut` calls run at different free pointers with junk tails `[P+128, P+159)` (`hashLeafOut_deterministic`'s `hjunk`); tying level-0 node content to `decodeLeaf3` across the history needs a per-index leaf-hash cache pack (the `CachedLeaf` twin of the tri-anchor pack). Shape is known (#66), but it is an additional hypothesis surface the capstone will carry.
7. **`maxN` halving vs. frontier arithmetic.** `PassOK`/edge dispatch use `maxN >>> l` while M-C uses `⌈count/2^l⌉`; the equivalence (`maxN = count − 1` pre-bump vs. `count` post-bump on walk #2, where `idx = maxN` initially) is exactly the off-by-one minefield of `FullMerkle.sol:53-64` — recommend proving M-C directly in `Fin.shiftRight` form.

**Ignore `specs/KDParallel/`** (untracked, untrusted) — nothing above depends on it.
