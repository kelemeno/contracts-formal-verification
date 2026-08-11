# Security Verification — Reviewer's Guide

**Purpose.** Every theorem below is *machine-checked* in Lean (the proofs are verified by the
Lean kernel). As a human reviewer you do **not** need to read the proofs. Your job is only to
decide two things:

1. **Do the STATEMENTS say what we want?** (Does each formal property faithfully capture the
   intended security guarantee?)
2. **Are the ASSUMPTIONS acceptable?** (The model + trusted base the statements rest on.)

If you agree with the statements and accept the assumptions, then the guarantees hold of the
**modeled** contract — that's what a machine-checked proof buys you.

This document is the contract between the proofs and a human auditor. Read Part A (assumptions)
first — it bounds what *any* statement here can mean.

---

## Executive summary — the security properties proven

In plain terms, the L1 bridge is now machine-checked (over the modeled contracts, per the Part A
assumptions) to guarantee:

- **Withdrawals can't be replayed** — a withdrawal finalizes at most once (nullifier checked-then-set). *(#1)*
- **Withdrawals can't skip proof verification** — finalizing a withdrawal necessarily checks a Merkle
  proof (`fun_verifyWithdrawal` is witnessed). *(#20; together with #1 these are the two core
  withdrawal guarantees — both modulo the admitted MCOPY/TSTORE opcodes, A3.)* And the **public**
  `finalizeWithdrawal` entry provably routes through the modifier carrying both, so these hold of the real
  API, not just the modifier. *(#21)*
- **Only authorized callers reach the gated/fund-moving functions** — owner-only (#5/#17), not-when-paused
  (#6/#18), Bridgehub-only (#15), and NativeTokenVault-only on the actual fund-mover `transferFundsToNTV`
  (#16). For #17/#18 in the strong form: *a successful guard ⇒ the precondition genuinely held.*
- **Ownership transfers correctly** — the owner slot ends up holding the new owner. *(#2)*
- **Chain registration is validated and committed correctly** — it routes through all 9 validation gates
  (success ⇒ gates 1–8 held, #4/#19), and writes the chain to the right keccak-derived slot (#3); the
  EnumerableMap backbone reads/writes the correct slots (#10–12).
- **Custody is conserved through bridging** — a "success" custody result requires the balance-difference
  guard (#7), and the same amount flows unchanged into the bridge encodings (#8).
- **The diamond proxy routes each selector to its correct registered facet** — dispatch slot =
  `keccak(selector‖DIAMOND_POSITION)` (#13) and the decoded facet = `address(sload(that slot))` (#14).

**Atomic interop (era-contracts PR #2218), added 2026-07-11 — the bridge's delivered-XOR-reclaimed
story:**

- **No double refund** — a refund pays out only from an authorized (`Revertable`) leg, at most once
  (*#22*), and **no theft via crafted bundle bytes** — a claim is slot-bound to the exact committed
  bundle hash (*#23*, A6′).
- **Both verification gates are pure mathematics** — the Merkle path recomputation is the pure fold
  `foldRoot` (*#24*), delivery accepts only proofs folding to the authenticated root (*#25*), and
  the reclaim absence-witness verifier is fully characterized (*#26*).
- **The committed root binds everything** — same position + same root ⇒ same leaf hash (*#27*, A6′)
  ⇒ same leaf fields (*#28*, A6′) ⇒ same `(flowId, bundleHash)` leg identity (*#33*, A6′; the
  commit value the tree stores is injective in the leg, and its closed form is axiom-free); a
  delivered member and a reclaim gap cannot share a position (*#29*) nor coexist in any `GapSound`
  tree (*#30* abstract invariant + insert preservation; capstone
  `committed_member_gap_impossible`), and **never both across time** — on-time membership and a
  deadline-pinned gap witness for the same leg are jointly impossible along any append-only IMT
  history with monotone settlement timestamps (*#34*, axiom-free) — and **never neither**: an
  absent leg always HAS a valid reclaim witness, at every snapshot (*#35*, axiom-free). These two
  are packaged into one **exactly-one-outcome capstone**
  (`timed_out_leg_reclaimable_not_deliverable`, axiom-free): a timed-out leg (nonzero commit value
  absent from a deadline-pinned snapshot) is reclaimable AND is a key of no on-time snapshot. The
  bound is further sharpened to an **equivalence** (*#35b*, `reclaimable_iff_absent`, axiom-free): a
  nonzero leg is reclaimable at a snapshot **iff** it is absent there — so the reclaim gate fires on
  exactly the never-delivered legs (a delivered leg can never also be refunded, and an undelivered
  one is always witnessable). The
  timeout gate's compiled guards enforce exactly #34's premises: acceptance forces
  `tN ≤ deadline < tS` with consecutive batches (*#36*, axiom-free, both directions), and the
  flow structure both gates run under is canonical and flowId-bound — sorted legs, aligned
  chain-ids, recomputed hash — before any proof is examined (*#37*, axiom-free), with every root
  attested by the message-verification contract and every clock anchored to the settlement layer
  (*#38*, axiom-free).
- **The tree-builder is verified against a pure model** — `fun_updateLeaf` end-to-end equals the
  pure walk `updateWalk` (leaf write + per-level sibling hash + parent store) (*#31* + U4), and
  **the gates' verifier fold replays that walk** — given the walk's cache, siblings, and scratch
  window, `foldRoot` recomputes exactly the stored root (*#32*, axiom-free), and **the stored root
  admits ONLY the written leaf** — any collision-free fold reaching it at that position carries
  the builder's leaf (`root_pins_written_leaf`, *#32* + *#27*, A6′).
- **The insert protocol is machine-checked down to its storage writes** — the three
  leaves-mapping primitives have closed forms (*#39*: slot accessor `keccak(i‖4)`, struct
  read/write); the pointwise write effect is discharged against the real storage model (*#41*,
  `[propext, Quot.sound]` only); distinct keys give keccak-separated slot triples (A6″); and the
  abstract insert-effect bridge (*#40*) turns those pointwise facts into `imtInsert` with ALL
  FOUR invariants (`GapSound`/`KeyInj`/`RepKeyInj` + effect) carried inductively — uniqueness and
  value-freshness are DERIVED (from `RepKeyInj` and the gap window), not assumed. Capstone: any
  concrete storage history of such steps — growth inserts and node-only writes included via the
  pointwise formulation — is an `Evolution` with every invariant at every snapshot (*#42*), so
  never-both (#34) and never-neither (#35) apply to the real tree directly.
- **The flow identity binds its own terms** — equal keccak outputs pin the preimage interval,
  every fixed-offset word, and the LENGTH (*#43*, the pinning principle); instantiated: equal
  flowIds carry equal deadlines, settlement-layer clocks, encoding lengths, and leg counts
  (*#44*, through the compiled encoder's layout, with the `calldatacopy` frame proving the heads
  survive the dynamic-array copies). With #33 (commit values bake the flowId in) and #37: the
  deadline every guard compares against is the one fixed at deposit time, per leg, through the
  tree commitment.
- **Model boundaries, made explicit** — external calls are opaque in Clear (`staticcall` returns
  no values), so the message-verification RESULT is inherently a hypothesis; the decode boundary
  around it is machine-checked (the flag is the verifier's word, boolean-or-revert, #38 update).
  The remaining non-mechanized step is the dispatcher-inlined insert glue → `imtInsert`
  correspondence (source-level inspection; the generator does not extract dispatcher bodies).

45 machine-checked theorem groups in total (Part B), on top of a 485/485 real-build baseline (A9). The
numbers in parentheses are the theorem entries below. Caveats per theorem are in Part B; the trusted
base is Part A.

---

## Part A — Assumptions & Trusted Base (read this first)

These are the things you must accept. They are NOT proven; they are the foundation.

**A1. Source → model translation.** Each contract is compiled Solidity → optimized Yul IR
(`solc 0.8.28`, `--optimize --ir-optimized`) → Clear's Lean AST. **You trust solc and the Yul→Lean
importer.** The Yul we verify is in `yul/<Contract>.yul`; the Lean AST is in `generated/`. A
reviewer can spot-check that the Yul matches the Solidity.

**A2. EVM semantics.** Clear's `State` / `exec` / `eval` / `sload` / `sstore` / `keccak256` / `call`
(in the `Clear/` framework, `Clear/Clear/EVMState.lean`, `Interpreter.lean`) faithfully model the
EVM. **You trust this EVM model.**
**A2a. KNOWN fidelity gap (machine-checked, `specs/ModelFidelity.lean`).** `Array.extractFill`
computes `extract v₀ (v₀ + size − 1)` with an EXCLUSIVE stop, returning `size − 1` elements — so
the modeled `calldataload` reads 31 bytes: **the low byte of every modeled calldata word is 0**
(witness: an all-`0xFF` 32-byte read has `.val % 256 = 0`; the high byte is read correctly), and
`calldatacopy` inherits the same truncation via `extractBytes`. Impact: none of the theorems in
Part B depends on concrete calldata bytes (values are treated symbolically); the gap WOULD affect
content-level claims (e.g. "the copied array element equals the calldata word") and concrete
replays. Flagged for an upstream Clear fix; the witnesses pin the behavior so the fix is
observable. Also note external calls (`staticcall` etc.) return NO values in the model — results
of cross-contract calls are hypotheses by construction (see #38).

**A3. Admitted opcodes (MCOPY, TSTORE).** `solc 0.8.28` emits `mcopy` (EIP-5656) and `tstore`
(EIP-1153, transient storage), which Clear does not natively model. They are supplied as small
hand-written modules with an **admitted** abstraction lemma (`mcopy_abs_of_code`,
`tstore_abs_of_code` — proved by `sorry`). **These two opcodes' semantics are assumptions, not
proofs.** Transient storage (used for the reentrancy guard / pause flags) is modeled as having no
observable persistent effect.

**A4. Revert model — IMPORTANT.** Clear models `revert(a,b)` as writing return-data and leaving the
machine state `Ok` (it does **not** mark a distinct "reverted/halted" state;
`EVMState.lean:evm_revert`). **Consequence:** a guard property cannot be stated as a clean
"a successful (non-reverting) return implies the precondition holds." Instead, guard theorems
below are stated as **"the contract computes the correct guard condition and routes through the
revert sub-block"** — i.e. they prove the contract *checks the right thing*, not a state-level
success⇒precondition. **UPDATE:** Clear's revert model has now been extended with a `reverted : Bool`
flag on the EVM state (set by `revert`), so a reverted end-state IS now distinguishable from a successful
one. Theorem **#17 uses this to state the clean success⇒precondition form for `checkOwner`.** The remaining
guard theorems (#4, #6, #15, #16) are still in the older "computes the right condition" form pending the same
upgrade. (The flag change currently lives in the local Clear dependency checkout — see #17's caveat.)

**A5. Sub-call abstraction.** A function's behavior is expressed in terms of the abstract specs of
the sub-blocks/sub-calls it invokes. Some of those sub-specs are *thin-wrappers* (definitionally the
concrete code). So when a theorem says "the call routes through sub-block X," it means X executed;
X's own deeper internal effect may be one abstraction layer further down.

**A6. keccak / storage non-aliasing.** keccak slots are modeled by a freshness mechanism
(`EVMState.lean`). We have a proven, axiom-free lemma (`Clear.KeccakDistinct.sload_sstore_of_ne`)
that a write at slot `b` preserves reads at any `a ≠ b`, plus sequential-keccak distinctness. The
freshness model alone does **not** give full keccak injectivity, so some storage-write theorems are
proven at the **point of the write (mid-execution)** rather than "survives to end-of-call," unless
the slot is fixed (non-keccak).
**A6′ (opt-in trusted-base extension).** `specs/KeccakInjective.lean` adds an **explicit axiom**
`keccak256_inj` — distinct preimages ⇒ distinct keccak slots (the standard collision-resistance ≈
injectivity idealization) — and a non-aliasing corollary `sload_sstore_keccak_of_preimage_ne`
(a write at `keccak(P₂)` preserves a read at `keccak(P₁)` when `P₁ ≠ P₂`). This enlarges the trusted
base **only for theorems that use it**: any such theorem lists `Clear.KeccakInjective.keccak256_inj`
in its `#print axioms`. It is the enabler for upgrading mid-execution storage writes to end-of-call
across *different* keccak-derived slots. As a worked demonstration, the file proves
**unconditionally** (`enumerablemap_values_indexes_slots_distinct'`) that EnumerableMap's `_values[k]`
slot `keccak(k‖210)` and `_indexes[k]` slot `keccak(k‖209)` are distinct given only the standard
mapping-slot `mstore(32, baseSlot)` layout — the exact non-aliasing fact that blocks end-of-call
storage upgrades — via a from-scratch, kernel-checked `mstore`/`lookupMemory` round-trip (axiom-clean
apart from `keccak256_inj`). The file also adds two further (sanctioned) idealization axioms —
`keccak256_ne_lowSlot` (a keccak slot never equals a reserved low slot `< 2³²`) and `keccak256_slot_sep`
(an array element `keccak(P₁)+i`, small `i`, never aliases a mapping slot `keccak(P₂)`, `P₁≠P₂`) — used to
prove a **conditional** end-of-call non-aliasing theorem for chain registration
(`fun_registerNewZKChain_value_survives_fun_add`: given `fun_add`'s success-path 3-write storage trace, the
registered chain address at `keccak(chainId‖210)` survives the keys-length / keys-array / `_indexes` writes).
**None of theorems #1–#20 depend on any of these axioms** — they are opt-in infrastructure; the conditional
end-of-call theorem is a separate, clearly-axiom-tagged result. (The *unconditional* #3 end-of-call is still
out of reach, but now only because materializing `fun_add`'s switch spec hits a term-size blowup — the keccak
non-aliasing half is solved.) A reviewer who rejects these idealizations can disregard them without affecting
#1–#20, whose `#print axioms` are free of all three keccak axioms.

**A7. Storage slot numbers.** Slot constants in the statements are read from the compiled Yul.
**All slot→variable bindings have now been cross-checked against the compiler's own `@src` source
annotations (2026-06-09)** — the table below lists each constant, the `@src`-tagged Solidity variable
it resolves to, and the theorem that relies on it:

| Slot | `@src` variable | used by |
|------|-----------------|---------|
| `51` (`0x33`) | `_owner` (Ownable) | every `onlyOwner` guard (#2, #17) |
| `151` (`0x97`) | `_paused` (Pausable, mask 255) | requireNotPaused (#18) |
| `201` (`0xc9`) | `assetRouter` | validateChainParams "shared bridge set" gate (#19) |
| `202` (`0xca`) | `chainTypeManagerIsRegistered` | validateChainParams "CTM registered" gate (#19) |
| `204` (`0xcc`) | `chainTypeManager` | registerNewZKChain (#3) |
| `208` (`0xd0`) | `isWithdrawalFinalized` | replay protection (#1, #20, #21) |
| `209` / `210` | `set._indexes` / `map._values` | EnumerableMap backbone (#10–12) |
| `218` (`0xda`) | `assetIdIsRegistered` | validateChainParams "assetId supported" gate (#19) |

Each `mstore(0x20, <const>)` that forms a mapping slot carries an `@src` comment naming the Solidity
variable (e.g. the nullifier helper does `mstore(0x20, 0xd0)` tagged `"isWithdrawalFinalized"`); the
full nullifier CHECK is
`require_helper_error_WithdrawalAlreadyFinalized(cleanup_bool(iszero(read_from_storage_split_offset_bool(<triple-keccak from base 0xd0>))))`,
exactly the structure the replay proofs replay, and the SET writes the **same** base-208 triple-keccak
slot — so the replay theorems are confirmed **non-vacuous**. (Codegen note: the mapping-access helper
names like `…mapping_address_uint256…` are a Solidity artifact — one structural helper name is reused
across same-shape accesses — so the `@src` tag, not the helper name, identifies the variable. An earlier
revision of this paragraph mislabeled the gate slots; the theorems always used the correct bindings.)

**A8. Scope.** Each theorem is about a **single function execution in a single contract** (with one
cross-function exception now: #21 connects the public `finalizeWithdrawal` to its `modifier_nonReentrant_892`,
so #1/#20 reach the public API).
NOT covered: liveness ("deposited funds can *always* be withdrawn" — depends on L2 + prover, out of
model); full cross-contract end-to-end chains (external calls are abstracted per A5); the L2 side;
gas; and anything depending on the actual keccak hash function being collision-free beyond A6.

**A9. Baseline.** Separately from the deep theorems, **all 485 functions across the 4 contracts
compile under the Lean kernel** (real builds, verified). This establishes the Solidity→Yul→Lean
modeling is well-formed and internally consistent for the whole codebase — necessary groundwork, but
on its own it is *not* a behavioral claim.

---

## Part B — The Core Statements (22 machine-checked theorems)

Each entry: the **plain-English claim** (what to review), the **storage/quantity it concerns**, what
it **guarantees**, and the honest **caveat**. File paths are under `specs/`.

> **⚠️ Status note (in-progress regeneration).** The L1AssetRouter contract is mid-way through a generator
> regeneration (block-chunking rollout). **#7 (transferFundsToNTV custody) and #8 (amount conservation) have
> been re-derived and re-verified** against the new block layout (#8 re-stated at the `mstore` level: the same
> custody-observed `amount` flows unchanged into both the burn-data and L2-tx encoder memory writes). Only **#9
> (deposit-side custody)** remains **downgraded**, deferred as impractical to re-derive post-regen (its gen alone
> takes ~40–50 min to elaborate); its routing property still holds in meaning. So the honest current count is
> **15 deep (#1–#8, #10–#16) + 1 (#9) deferred** — which *exceeds* the pre-regeneration baseline of 14. Originals backed up.

> **⚠️ Migration blocker (2026-07-17, era-contracts → PR #2303 head `c67894b97`).** The atomic-interop
> contracts were re-generated against the updated source. Most repairs are mechanical (memory-pointer
> variable renames, block content-hash remaps, and one storage-layout shift: the `leaves` mapping moved
> from slot 4 → 5, fixed in `imt_leaf_storage`). The **abstract / keccak / storage layers**
> (`IMTAbstract`, the `imt_*` arc, #22–#44 as listed below) are unaffected and verify in isolation.
> **One structural generator gap blocks the concrete AtomicFlowManager function-execution layer** and
> hence `lake build specs` as a whole: the Clear VC generator emits `rw [EVM<Func>']` for control-flow
> **conditions that are user-function calls** (`if cleanup_bool(x)`, `switch read_from_calldatat_bool(x)`),
> treating them as primops. No such lemma exists, and the emitted `_concrete_of_code` goal is itself
> unprovable — `If'` evaluates the condition with universally-quantified fuel, and a user-function call
> diverges at fuel 0 while returning the real value at fuel ≥ 1, so no fuel-independent synthesized spec
> can match. Primop conditions escape this (fuel-independent); statement-position user calls escape via
> the generated `<f>_abs_of_code` abstraction; the condition path has no such mechanism. Affects 5
> generated Common blocks (2 user functions: `cleanup_bool`, `read_from_calldatat_bool`) and transitively
> the `fun_getProofData / fun_verifyInclusion_1261 / fun_authenticateRoot / fun_verifyTimeoutAbsence`
> proofs. **Fix requires generator work (condition-position abstraction scaffold + fuel-relative spec) —
> escalated, not a spec-repair.** Details in the `atomic-interop-verification` memory.

### 1. Withdrawal replay protection  — *the anti-bridge-drain property*
`L1Nullifier/.../modifier_nonReentrant_892_user.lean`
- **Claim:** every run of the withdrawal-finalization guarded body (a) **reads** the
  `isWithdrawalFinalized[chainId][batch][index]` flag (nullifier slot = triple-nested keccak over
  base slot 208), cleans it, and feeds it to the `WithdrawalAlreadyFinalized` require-helper —
  which reverts exactly when the flag is already set; and (b) **recomputes the slot and writes the
  flag = true**.
- **Guarantees:** a *first* finalization sets the nullifier; a *replay* of the same withdrawal is
  routed through the revert. → no double-withdrawal.
- **Source-ordering cross-check (2026-06-09):** `_finalizeDeposit` (`L1Nullifier.sol:434`) is
  `nonReentrant whenNotPaused` and follows strict checks-effects-interactions:
  `require(!isWithdrawalFinalized[...])` (438, CHECK) → `isWithdrawalFinalized[...] = true` (439, SET)
  → `_verifyWithdrawal(...)` and fund release (441+, INTERACTION). The nullifier is set **before** any
  external value movement, so the "flag set ⇒ revert" theorem actually closes the replay window (a SET
  placed after the interaction would leave it open). The proof's witness ordering (CHECK =
  `block_4604436955705083701`, SET = `block_4633566561656549981`, which contains the `verifyWithdrawal`
  call) matches this source ordering.
- **Caveat:** stated as the existence of those sub-block executions (read→cleanup→require, then
  accessor→write). Per A4, "reverts on replay" is the require-helper's witnessed behavior, not a
  state predicate. **Remaining gap (narrowed 2026-06-09, closed 2026-07-10):** both *sides* of the
  loop are proven A3-free as state predicates (see #1b for the CHECK side and the SET-write lemmas
  below); the last piece — the **slot-equality** linkage, that the read slot `split_expr_7` equals
  the write slot `split_expr_13` — is now **proven** at statement level (`check_set_slots_eq`, see
  the slot-equality entry below): the two triple-nested keccak accessor chains over the same params
  `(_1,_2,_3)` provably return the same slot, because Clear's keccak memoizes each hashed preimage
  and the re-run replays the cache. What remains "by construction" is only lifting that
  statement-level chain to the two blocks' replay (the six accessor calls appear verbatim in the
  blocks; wiring their execCall equations through the block AST is mechanical).
- **SET-write lemmas (`no_replay_user.lean`, A3-free, added 2026-06-09):** `update_storage_writes_flag`
  gives the closed form of the nullifier write `sstore(slot, (sload(slot) & ~255) | 1)`, and
  `update_storage_sets_low_byte` proves the post-write byte is exactly `1` (so `≠ 0`) — i.e. the SET
  genuinely sets the finalized flag. This is precisely the `hset` precondition the #1b CHECK theorem
  reverts on, so the two compose into the full loop (modulo the slot-equality linkage above). `#print
  axioms` = `[propext, Quot.sound, Classical.choice]`, no `sorryAx` (the lemmas touch only
  sload/and/or/sstore, never `fun_verifyWithdrawal`). (`update_storage_sets_low_byte` carries the
  benign hypothesis that the contract's own account exists — always true for a deployed contract.)
- **End-to-end composition (`replay_after_set_reverts`, A3-free, added 2026-06-10):** chains the two
  halves into one theorem — *run the nullifier write at `slot`, then run the CHECK block with
  `split_expr_7 ↦ slot` on the post-write evm ⇒ the run ends `reverted = true`.* The byte the SET writes
  is literally the byte the CHECK reads (the post-write evm is fed straight into the CHECK), so this is a
  genuine composition, not re-hypothesized. `#print axioms` = `[propext, Quot.sound, Classical.choice]`.
  The shared variable `slot` is the honest stand-in for the slot-equality link, itself now proven:
- **Slot-equality — CHECK slot = SET slot (`check_set_slots_eq`, A3-free, axiom-clean, added
  2026-07-10):** `no_replay_user.lean` + the new axiom-free `specs/KeccakDeterminism.lean`. Running
  the triple accessor chain twice with the same keys `(_1,_2,_3)` and base slot 208 — the CHECK
  chain (`split_expr_5/6/7`) and the SET chain (`split_expr_11/12/13`) — returns the **same** final
  slot. Mechanism (model-derived, no axioms): each `mapping_index_access` writes `key`/`base` to
  scratch `[0,64)` and hashes it; Clear's freshness model memoizes every hashed preimage in
  `keccak_map`, so the SET-side re-run *hits the cache at every level*. Honest frame hypotheses
  (both true of the actual intervening sload/iszero/cleanup/require-success statements): memory
  bytes `[64,95)` unchanged (the model's `lookupMemory` makes the 64-byte hash interval depend on
  that junk window too — the unconditional preimage-equality is FALSE in the model and an earlier
  broken general form was removed from `KeccakInjective.lean`), and no keccak-cache entry dropped.
  Plus the A6-style caveat hypothesis that no hash-collision fallback fired on the CHECK side.
  `#print axioms check_set_slots_eq` = `[propext, Quot.sound, Classical.choice]` — no `sorryAx`,
  no keccak axioms. Scope: stated over the six accessor `execCall`s (which appear verbatim in the
  CHECK/SET blocks) rather than re-derived through the block ASTs.

### 1b. Cross-transaction replay revert  — *the anti-double-spend property, as a state predicate*  ✅ A3-free, axiom-clean
`L1Nullifier/.../no_replay_user.lean` — theorem `replay_protection_check_reverts` *(added 2026-06-09)*
- **Claim:** running the replay-CHECK block `block_4604436955705083701` of `finalizeWithdrawal` from a
  state whose persistent nullifier flag is **already set** ends `reverted = true`. Precondition:
  `store["split_expr_7"] = slot` (the precomputed `isWithdrawalFinalized[chainId][batch][index]` slot
  entering the block) and `Fin.land (evm.sload slot) 255 ≠ 0` (its finalised low byte is set).
- **Why it strengthens #1:** #1 witnesses the check→cleanup→require *executions*; this states the
  *security consequence as a state predicate* — already-finalized ⇒ the run ends in the `reverted`
  state (using the RevertModel `reverted` flag, A4). It is the genuine **cross-transaction** form the
  per-call `nonReentrant` does not by itself give: from *any* prior state with the flag set, re-running
  the guard reverts. Polarity verified against the Yul (read `and(sload,255)` → `iszero`(→0 when byte
  set) → `cleanup_bool`(→0) → `require_helper_error_WithdrawalAlreadyFinalized(0)` reverts), and the
  trailing `mapping_index` keccak recompute is proven to preserve the revert.
- **Axioms:** `#print axioms` = `[propext, Quot.sound, Classical.choice]` — **no `sorryAx`, no keccak
  axioms**. Cleaner than #1/#20: because the CHECK reverts *before* the SET block calls
  `fun_verifyWithdrawal` (the only transitive source of the admitted `mcopy`/`tstore` stubs), this
  theorem never reaches A3. So it is **not** "modulo A3" — it is fully discharged to the standard kernel
  axioms.
- **Caveat (honest scope):** stated at the decisive **CHECK-block** level, not threaded through the
  full 15-block modifier prelude (reentrancy/`whenNotPaused`/keccak-slot computation). The precondition
  is pinned faithfully on the CHECK block's genuine input slot `split_expr_7`; the prelude is orthogonal
  to the replay content. Requires `fuel+1` (any successor fuel — the block is straight-line).

### 2. Ownership-transfer integrity  — *root of access control*  ✅ clean end-of-call
`L1Bridgehub/.../fun_transferOwnership_user.lean`
- **Claim:** after the call, the owner storage slot **51** (the exact slot every `onlyOwner` guard
  reads) holds, in its address bits, the new owner: `s₉.sload(51) & (2¹⁶⁰−1) = newOwner & (2¹⁶⁰−1)`.
- **Guarantees:** ownership is actually transferred to the intended address (end-of-call, survives
  the rest of the call — slot 51 is fixed, not keccak).
- **Caveat:** conditional on the new owner address being non-zero and the contract account existing
  (the genuine transfer case). Clean otherwise.

### 3. Chain-registry integrity  — *gateway migration*
`L1Bridgehub/.../fun_registerNewZKChain_user.lean`
- **Claim:** registering a chain stores the (masked) chain address at
  `keccak256(chainId ‖ 210)` = `_zkChainMap._values[chainId]` — **the same slot `get` reads back**
  (see #10) — and then runs `fun_add` (the enumerable-map keys-side registration).
- **Guarantees:** a registered chain's address is committed to its mapping slot.
- **Caveat:** proven at the point the value is handed to `fun_add` (**mid-execution**, per A6),
  conditional on `address(zkChain) ≠ 0` and the contract account existing.

### 4. Chain-parameter validation
`L1Bridgehub/.../fun_validateChainParams_user.lean`
- **Claim:** a chain registration provably routes through **all 9 validation gates** in order:
  chainId ≠ 0; chainId ≤ 2⁴⁸−1; chainId ≠ current chain; CTM address ≠ 0; assetId ≠ 0;
  CTM registered (slot 202); assetId supported (218); shared bridge set (201); not already
  registered (204).
- **Guarantees:** none of these checks can be skipped on the registration path.
- **Caveat:** gates 1–5 (storage-independent conditions) are pinned exactly; gates 6–9
  (storage-dependent) are witnessed as executing in sequence. Per A4, "rejects bad params" is
  routing-through-revert-blocks, not a success-state predicate.

### 5. Access control — owner check  (`checkOwner`)
`L1Bridgehub/.../fun_checkOwner_user.lean`
- **Claim:** the guard the contract computes is **exactly** `owner() == caller()`, where
  `owner = sload(51) & (2¹⁶⁰−1)` and `caller = execution_env.source`; the function's effect is that
  owner-checking if-block (which reverts iff the guard is false).
- **Guarantees:** the contract checks the *right* condition for owner-gating.
- **Caveat:** per A4, the consequence ("revert iff not owner") is the if-block's behavior, not a
  clean success⇒owner state predicate.

### 6. Pause enforcement  (`requireNotPaused`)
`L1Bridgehub/.../fun_requireNotPaused_user.lean`
- **Claim:** either the contract is **not paused** (`sload(151) & 255 = 0`), or execution went
  through the revert if-block. The paused flag is the Pausable `_paused` bool at slot 151, mask 255.
- **Guarantees:** the pause check reads the correct flag and reverts when paused.
- **Caveat:** per A4 (disjunction form: not-paused OR routed-through-revert).

### 7. Custody — withdrawal side  (`transferFundsToNTV`)
`L1AssetRouter/.../fun_transferFundsToNTV_inner_user.lean`
- **Claim:** a successful return (`var = 1`) is only possible when the final balance-check block
  does **not** fall through normally — i.e. control left via `leave`, the control-flow witness that
  the `require(balanceAfter − balanceBefore == amount)` guard passed. Falling through forces `var = 0`.
- **Guarantees:** you can't get a "success" custody result without the balance-difference guard
  having held.
- **Caveat:** the deeper numeric fact (`balanceAfter − balanceBefore = amount`) lives inside the
  final check block, whose spec is a thin-wrapper (A5) — so this proves the *control-flow* witness
  of the guard, with the exact equality one layer down.

### 8. Custody — amount conservation across encoding  (`bridged_amount_preserved`)
`L1AssetRouter/.../bridged_amount_preserved_user.lean`
- **Claim (conditional):** **given** the custody observation `balanceAfter − balanceBefore = amount`,
  the burn-data encoding and the L2-transaction encoding both carry **the same `amount`** through —
  the value isn't altered between taking custody and what gets bridged.
- **Guarantees:** the amount escrowed is the amount propagated into the bridge message.
- **Caveat:** a *conditional* theorem — it takes the custody balance-difference as a hypothesis and
  shows consistent propagation; it does not re-derive the custody fact here (#7 does the custody side).

### 9. Deposit-side custody  (`bridgehubDepositNonBaseTokenAsset`)
`L1AssetRouter/.../fun_bridgehubDepositNonBaseTokenAsset_user.lean`
- **Claim:** a deposit run necessarily routes through the internal `getDepositCalldata` sub-call
  (after taking custody via `bridgeBurn`), i.e. the deposit computes the L2 bridge-mint calldata
  used in the returned transaction request. Plus the conditional amount-preservation theorem (#8)
  specialized here.
- **Guarantees:** the deposit-side control flow goes through custody + the bridge-mint encoding.
- **Caveat:** sub-call-witness depth (A5); pinning the inner args end-to-end was intractable
  (large terms).

### 10–12. EnumerableMap correctness  (`get`, `tryGet`, `add`)
`L1Bridgehub/.../fun_get_user.lean`, `fun_tryGet_user.lean`, `fun_add_user.lean`
- **`get`:** returns `sload(keccak256(key ‖ 210))` — i.e. `map._values[key]`, the same slot `add`
  writes and `registerNewZKChain` (#3) stores into. (Reverts on absent key, witnessed.)
- **`tryGet`:** the found-flag equals "key present" (its `_indexes[key]` is non-zero), and the
  returned value is the stored value at the keccak slot.
- **`add`:** the freshness guard equals `iszero(sload(valueSlot))` (new-key detection) and the call
  routes through the storing switch (which writes the value, key, and index slots).
- **Guarantees:** the chain-registry map reads/writes the correct keccak-derived slots — this is the
  data-structure backbone the registry theorems (#3, #4) build on.
- **Caveat:** `add`'s actual write is inside the storing switch (thin-wrapper, A5); `get`/`tryGet`
  pin the read slot + return plumbing.

### 13. Facet-routing slot computation  (DiamondProxy / EIP-2535)  ✅ clean
`DiamondProxy/.../mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_user.lean`
- **Claim:** the dispatch slot the proxy computes for a function `selector` is **exactly**
  `keccak256( bytes4(selector) ‖ DIAMOND_STORAGE_POSITION )` — the genuine Solidity slot of
  `ds.selectorToFacet[selector]`. The base constant is verified equal to
  `keccak256("diamond.standard.diamond.storage") − 1` (era-contracts `Diamond.sol`), and
  `selectorToFacet` is field 0 of that struct (mapping rooted at the base).
- **Guarantees:** the fallback looks up the facet record at the correct, collision-resistant storage
  slot derived from the incoming selector — it cannot be made to read a different mapping.
- **Caveat:** returns `0` on a keccak hash-collision, mirroring the EVM model (A6); clean otherwise.

### 14. Facet-record decode  (DiamondProxy / EIP-2535)  — *completes the routing read*
`DiamondProxy/.../read_from_storage_reference_type_struct_SelectorToFacet_user.lean`
- **Claim:** decoding the packed word `w = sload(slot)` at that slot yields, in memory, the
  `SelectorToFacet` struct with **facet address = `w & (2¹⁶⁰−1)`** (low 160 bits),
  selectorPosition = `(w >> 160) & 0xFFFF`, isFreezable = `(w >> 176) & 0xFF ≠ 0` — all three fields
  pinned exactly to the masked/shifted storage word, and the returned pointer is the fresh struct.
- **Guarantees:** combined with #13, the facet the proxy will `delegatecall` is exactly
  `address( sload( keccak256(selector ‖ DIAMOND_STORAGE_POSITION) ) )` — the routing target is the
  registered facet for that selector, not an attacker-chosen address.
- **Caveat:** conditioned on one standard well-formedness hypothesis — the free-memory-pointer
  arithmetic does not overflow (the path the contract executes; the overflow path reverts). The
  actual `delegatecall` dispatch itself (the step after the lookup) is not yet a separate theorem.

### 15. Fund-mover authorization — Bridgehub-only check  (L1AssetRouter, *partial*)
`L1AssetRouter/.../bridgehub_caller_guard_user.lean`
- **Claim:** for the Bridgehub-gated entry (selector `0x8eb7db57`), the contract computes the authorization
  comparison `msg.sender == address(BRIDGE_HUB)` from the **genuine** operands: the caller side is exactly
  `execution_env.source`, and the authorized side is exactly `BRIDGE_HUB_immutable & (2¹⁶⁰−1)` (the masked
  immutable). The guard literal the dispatcher tests equals `fromBool(source == authorizedAddress)`.
- **Guarantees:** the access check on this fund-moving path reads the *real* caller and compares it against the
  *real* (masked) BRIDGE_HUB immutable — it cannot be tricked into comparing against the wrong value.
- **Caveat (important — this is weaker than #5/#6):** the actual `eq` comparison and the revert-routing are
  inlined in the contract's giant dispatch switch, which is currently too heavy to compile, so this theorem
  pins the two **operands** and the guard **literal**, but does **not** itself execute the comparison or prove
  "reverts when caller ≠ BRIDGE_HUB." Also `loadimmutable` is opaque in the model, so BRIDGE_HUB is the
  immutable value modulo the assumption "immutable slot 75 = BRIDGE_HUB address" (a slot-number-style
  assumption, cf. A7). Per A4, revert-routing is not a state predicate regardless.

### 16. Fund-mover authorization — NativeTokenVault-only check  (L1AssetRouter, *strongest auth guard*)
`L1AssetRouter/.../ntv_caller_guard_user.lean`
- **Claim:** for the NTV-gated fund-mover entry (selector `0x57d4ca5c`, `transferFundsToNTV`), the contract
  computes the authorization comparison `msg.sender == address(nativeTokenVault)` from the **genuine** operands:
  caller = `execution_env.source`, and the authorized side = `sload(251) & (2¹⁶⁰−1)` — i.e. the
  NativeTokenVault address read from **storage slot 251 (0xfb)**. The guard literal equals
  `fromBool(source == sload(251) & mask)`.
- **Guarantees:** the access check on the path that moves funds into the NativeTokenVault reads the real caller
  and compares it against the real, **storage-resident** NTV address — strictly stronger than #15 (whose
  authorized address came from an opaque immutable).
- **Caveat:** as with #5/#15, the `eq` + revert-routing is inlined in the giant dispatch switch (too heavy to
  compile), so this pins the two operands and the guard literal, not the revert routing itself (A4). The only
  real-chain assumption is slot 251 = `nativeTokenVault` (cf. A7), which the Yul source confirms.

### 17. Access control — *clean* owner check  (`checkOwner`, success ⇒ precondition)  ✅ NEW form
`L1Bridgehub/.../fun_checkOwner_clean_user.lean` (+ framework helper `specs/RevertModel.lean`)
- **Claim:** if `checkOwner` runs from a fresh (non-reverted) state and the run's **final state is itself
  non-reverting**, then the caller **was** the owner: `s₉.evm.reverted = false → (sload(51) & (2¹⁶⁰−1) =
  caller)`. I.e. a *successful* `onlyOwner` check implies `owner() == msg.sender` actually held.
- **Guarantees:** this is the strong, intuitive access-control statement — strictly stronger than #5 (which
  could only say the contract *computes* the right boolean and routes through revert). It is enabled by a new
  Clear framework feature: a `reverted` flag on the EVM state, set by `revert`, so a reverted end-state is now
  distinguishable from a successful one (lifting the A4 limitation for this theorem).
- **Caveat:** requires the start state to be non-reverted (`evm.reverted = false`, the intended fresh-entry
  precondition). The `reverted`-flag framework change currently lives in the local Clear dependency checkout
  (its durable home is upstream Clear + a lakefile pin). The same pattern can upgrade #4/#6/#15/#16 to this
  clean form (not yet done for those).

### 18. Pause enforcement — *clean* form  (`requireNotPaused`, success ⇒ precondition)  ✅ NEW form
`L1Bridgehub/.../fun_requireNotPaused_clean_user.lean`
- **Claim:** if `requireNotPaused` runs from a fresh (non-reverted) state and the run's final state is
  non-reverting, then the contract was **not paused**: `s₉.evm.reverted = false → (sload(151) & 255 = 0)`.
- **Guarantees:** the clean success⇒precondition reading of `require(!paused())` — strictly stronger than #6.
  Second demonstration (after #17) that the new `reverted` flag generalizes across standalone guards.
- **Caveat:** same as #17 — non-reverted start precondition; codegen-AST-tied; framework flag in the local
  Clear checkout pending upstreaming.

### 19. Chain-parameter validation — *clean* form  (`validateChainParams`, success ⇒ gates held)  ✅ NEW form
`L1Bridgehub/.../fun_validateChainParams_clean_user.lean`
- **Claim:** a non-reverting (successful) `validateChainParams` run implies **8 of the 9 validation gates
  actually held**: `chainId ≠ 0 ∧ ¬(chainId > 2⁴⁸−1) ∧ chainId ≠ block.chainid ∧ (chainTypeManager &
  (2¹⁶⁰−1)) ≠ 0 ∧ assetId ≠ 0` (gates 1–5, storage-independent) **and** gate 6 (CTM registered) ∧ gate 7
  (assetId supported) — each `∃ slot, (sload slot) & 255 ≠ 0` — ∧ gate 8 (shared bridge set: `sload(201) &
  (2¹⁶⁰−1) ≠ 0`).
- **Guarantees:** strengthens #4 from "routes through the gates" to "success ⇒ each gate's condition held"
  for 8/9 gates — the third demonstration that the `reverted` flag generalizes (across a 9-gate function with
  keccak-branching storage reads, via per-statement `reverted`-monotonicity + per-gate extraction).
- **Caveat:** gate 9 (BridgeHubAlreadyRegistered, slot 204) is carried by the monotonicity machinery (a
  failure there still reverts) but its condition is *not* extracted — it has a double-`iszero` guard and the
  keccak case-fanout exceeded the heartbeat budget. Gates 6/7 slots are pinned existentially (the model picks
  keccak slots non-deterministically). Same non-reverted-start precondition and codegen-AST dependence as #17/#18.

### 20. Proof-required-for-withdrawal — *no withdrawal without a verified Merkle proof*  ★ NEW
`L1Nullifier/.../modifier_nonReentrant_892_user.lean` (`proof_required_for_withdrawal`)
- **Claim:** a non-reverting run of the withdrawal-finalization guarded body necessarily **witnesses a call to
  `fun_verifyWithdrawal`** (the Merkle/L2-message proof verification) — i.e. the nullifier flag-write and the
  proof verification are inseparable; you cannot finalize a withdrawal without the proof being checked.
- **Guarantees:** together with #1 (replay protection), this closes the two core withdrawal-security
  properties: a withdrawal finalizes **at most once** (#1) and **only with a verified proof** (#20).
- **How it became provable:** this was whnf-walled for the whole effort (witnessing `fun_verifyWithdrawal`
  past the nullifier-set timed out at 40M heartbeats). The block-chunking regeneration isolated the verify
  call into its own Common block, so the witness is now a direct one-step extraction (no post-set chain
  traversal).
- **Caveat — trusted base:** this theorem (and the re-derived #1, see below) transitively use
  `fun_verifyWithdrawal`'s ABI decoding, which uses the **A3-admitted `MCOPY`/`TSTORE`** opcodes. So
  `#print axioms` shows `sorryAx` — sourced *only* from those two admitted-opcode modules (verified: they are
  the only `sorry`-bearing files in the cone; the proof itself is sorry-free). I.e. #20 and #1 are verified
  **modulo A3**, whereas most other theorems here are A3-free. Per A4, the property is the witnessed call, not
  a state predicate. (#1 was re-derived against the regenerated block-chunked layout — same property as before,
  now via a 15-block witness chain binding the CHECK and SET nullifier blocks; the re-derivation pulls the
  verify block in, hence its A3 dependency now.)

### 21. Public withdrawal entry routes through the nullifier modifier  ★ connects #1/#20 to the API
`L1Nullifier/.../fun_finalizeWithdrawal_user.lean` (`fun_finalizeWithdrawal_abs_of_concrete`)
- **Claim:** every non-reverting run of the **public** `finalizeWithdrawal` entry necessarily routes through
  `modifier_nonReentrant_892` — its 8th/final sub-block holds the `modifier_nonReentrant_892(memPtr)` call, and
  on the Ok (non-reverting-prefix) path the modifier's `Spec` holds on the intermediate states.
- **Guarantees:** the replay-protection (#1) and proof-required (#20) guarantees — proven on the modifier in
  isolation — therefore apply to the **actual public API**, not just the modifier. This narrows the
  single-function-scope limitation (A8) for the most security-critical entry point.
- **Caveat:** guarded by `isOk` of the modifier-block entry (a reverting decode prefix means the modifier
  doesn't run — faithful). It witnesses the modifier's *spec* by reference (control-flow routing), not a
  re-derivation. Same A3 dependency as #1/#20 (`sorryAx` only from the admitted `mcopy`/`tstore` via
  `fun_verifyWithdrawal`).

### 22. Atomic interop — refund state-machine safety / NO DOUBLE REFUND  ★ NEW (PR #2218 contracts)  ✅ A3-free, axiom-clean
`AtomicFlowManager/.../no_double_refund_user.lean` *(added 2026-07-10; contracts from era-contracts PR #2218
@ 37ad8bf1d — the atomic multi-leg interop module; `AtomicFlowManager` is the L2 built-in that coordinates
the timeout/refund path and re-mints burned source funds via `claimRefund`)*
- **Claim (CHECK side, `refund_check_reverts`):** running `claimRefund`'s CHECK block + guard-if from any
  state whose stored per-leg byte (`_state[flowId][bundleHash]`, low byte of the slot bound to
  `split_expr_21`) is a valid `LegState` **other than `Revertable(2)`** ends `reverted = true` (RevertModel
  flag, cf. #17). Instances: `Unset(0)` — a leg that never committed cannot be refunded; `Committed(1)` —
  no refund without `authorizeRefund`'s timeout proof; `Reverted(3)` — no re-refund.
- **Claim (SET side, `update_storage_sets_reverted_byte`):** the SET write helper stores exactly
  `Reverted(3)` into the slot's low byte (`sstore(slot, (sload(slot) & ~255) | 3)`, closed form +
  low-byte lemma).
- **Claim (end-to-end, `reclaim_after_refund_reverts`):** run the SET write at `slot`, then re-run the
  CHECK on the post-write evm ⇒ the re-claim REVERTS. **A leg is refunded at most once** — the leg-level
  anti-double-mint half of atomicity. (`claimRefund` flips the leg to `Reverted` *before* its external
  `_recoverBundle` calls — CEI — so this also covers the reentrant re-claim.)
- **Guarantees:** `claimRefund` pays out only a leg in state `Revertable` (set only by `authorizeRefund`
  after a verified IMT timeout-adjacency proof), and at most once.
- **Claim (slot-equality, `claim_check_set_slots_eq`):** the slot the CHECK reads (`split_expr_21`) equals
  the slot the SET writes (`split_expr_26`) — both are the same 2-level keccak accessor chain over
  `(flowId, bundleHash)` from base slot 0, and the re-run provably replays the cached keccak slots
  (`Clear.KeccakDeterminism.accessor_chain2_deterministic`, the 2-level analog of #1's `check_set_slots_eq`;
  frame hypotheses: bytes `[64,95)` unchanged + no cache entry dropped between the chains — true of the
  intervening read/validator/eq/guard statements; plus the A6-style collision-free hypothesis).
- **Caveat:** stated at the CHECK-block/guard-if/SET-helper/accessor level of the generated
  `fun_claimRefund` (the decode prelude and `_recoverBundle` are not re-derived); wiring the four accessor
  `execCall`s through the enclosing block ASTs is mechanical, as in #1. `hacc` (contract account exists) as
  in #1's SET lemmas. `#print axioms` for all four theorems = `[propext, Quot.sound, Classical.choice]` —
  no `sorryAx`, no keccak axioms. NOT yet covered: the finalize-side (`requireFlowFinalized`
  inclusion-proof witnessing — inlined in the dispatcher) and the deep IMT inclusion/absence mutual
  exclusion (the cross-path atomicity crux; needs IMT semantics + A6′).

### 23. Atomic interop — NO THEFT via the failed-deposit (refund) path  ★ NEW  ⚠ uses A6′
`AtomicFlowManager/.../no_theft_refund_user.lean` *(added 2026-07-11; contracts from era-contracts PR #2218)*
- **Interpretation (per the verification owner):** "theft" here means **value leaving to an unentitled
  party** — the payout must go only to whoever the committed bundle entitles — NOT a conservation-of-total-value
  invariant. All theorems in this section (and planned successors) are stated in that entitlement form.
- **The security question (beyond atomicity):** the state-machine theorems (#22) show a refund pays out only
  from `Revertable`, at most once — but *not* that the payout is bound to the **exact bundle bytes** committed
  at burn time. The theft scenario: an attacker calls `claimRefund(flowId, craftedBundleBytes)` with a
  different receiver/amount/calls, riding an authorization that `authorizeRefund` granted for the *honest*
  bundle. This theorem closes that gap.
- **Claim (`crafted_claim_reverts_after_authorization`):** let the honest bundle hash `k₁` resolve (via the
  `_state[flowId][·]` accessor) to storage slot `r₁`, and let an authorization be granted by *any* write at
  `r₁`. For ANY other bundle hash `k₂ ≠ k₁` whose leg was `Unset` before that write, the crafted `claimRefund`
  still ends `reverted = true`: (i) the accessor maps `k₂` to a **different** slot `r₂ ≠ r₁`
  (`accessor_slots_differ_of_key_ne`, from keccak injectivity — the two 64-byte accessor preimages differ at
  word 0, which holds the bundle hash); (ii) the authorization write at `r₁` is **invisible** at `r₂`
  (`sload_sstore_of_ne`, storage non-aliasing); (iii) so the crafted leg is still `Unset(0) ≠ Revertable(2)`,
  and `refund_check_reverts` (#22) fires.
- **Guarantees:** the refund payout is bound to the exact committed bundle hash. An attacker cannot substitute
  crafted bundle bytes to redirect or inflate a refund — the crafted claim reverts, funds are not stolen.
- **Caveat / trusted base:** uses the **A6′** keccak-injectivity axiom `Clear.KeccakInjective.keccak256_inj`
  (`#print axioms` = `[propext, Quot.sound, Classical.choice, keccak256_inj]`, no `sorryAx`). Scoped to the
  CHECK/guard-if level (as #22). The *other* half of the binding — different bundle BYTES ⇒ different
  `bundleHash` through `abi.encode(sourceChainId, bundle)` (`encodeInteropBundleHash`) — is the same
  idealization on the variable-length encoder and is the next step; combined they give: crafted bytes ⇒
  different hash ⇒ different slot ⇒ `Unset` ⇒ revert. The final fund-return correctness (that `_recoverBundle`
  re-mints to the **original depositor**) lives in `L2AssetRouter.recoverAtomicCall`, a separate contract
  (not yet compiled).

### 24. Atomic interop — IMT Merkle-path computation is a pure fold  ★ NEW  ✅ axiom-clean
`AtomicFlowManager/.../imt_hash_user.lean`, `imt_path_user.lean`, `imt_path_toplevel_user.lean`
*(added 2026-07-11; contracts from era-contracts PR #2218)*
- **What is proven (bottom-up, each layer a closed form over the one below):**
  (i) `efficientHash_call_acc` — the node-hash helper `fun_efficientHash(a,b)` returns exactly
  `keccak256(a ‖ b)` (the `accOut` scratch-memory hash) and touches nothing else;
  `efficientHash_deterministic` + `hashLeafOut_deterministic` (leaf hashing, chunk-wise over the
  generated Common blocks) pin both hash layers as functions of their inputs alone.
  (ii) `fold_loop` — the `for` loop of `fun_calculateRootMemory` equals the **pure recursion
  `foldRoot`**: at each level it reads the sibling from the caller-supplied proof array, orients by the
  index parity (`idx & 1`), hashes, halves the index, and recurses — the textbook Merkle-path fold.
  (iii) **`calculateRootMemory_call`** — the **whole function** (both Solidity bound-guards
  `depth < 256`, `index < 2^depth`, all initialisers, the loop, the return wire-up) equals
  `foldRoot` on the success path: `execCall fun_calculateRootMemory [v] (Ok evm store, [path, idx, leaf])
  = Ok (foldRoot …).2 (store.insert v (foldRoot …).1)`.
- **Why it matters for the bridge spec:** finalize (`requireFlowFinalized`) and the timeout/refund
  adjacency check both accept a leg only after `calculateRootMemory`-computed roots match the stored
  IMT root. This theorem replaces the ~50-statement Yul loop with a pure mathematical fold, so
  inclusion/exclusion arguments (the "delivered XOR reclaimed" crux, spec point 4) can now be made
  about `foldRoot` instead of about the interpreter.
- **Caveat / trusted base:** **axiom-free** — `#print axioms calculateRootMemory_call` =
  `[propext, Quot.sound, Classical.choice]`, no `sorryAx`, no keccak axioms (determinism only; no
  injectivity needed at this layer). Hypotheses: the two guard conditions hold (success path), the
  proof array lies in valid memory (`96 ≤ path`, no wraparound), `depth < 2^64`, and fuel
  `≥ 2·depth + 2`.

### 25. Atomic interop — the delivery gate REVERTS on a Merkle root mismatch  ★ NEW  ✅ axiom-clean
`AtomicFlowManager/.../inclusion_gate_user.lean` *(added 2026-07-11; PR #2218 contracts)*
- **Claim (`inclusion_root_mismatch_reverts`):** the tail of `fun_verifyInclusion` — the
  `fun_calculateRootMemory` call, the root comparison `var := eq(computedRoot, authenticatedRoot)`,
  and the guard-if `if cleanup_bool(iszero(var)) { revert }` — ends `reverted = true` whenever the
  submitted proof does NOT fold to the authenticated root:
  `foldRoot(evm, proof, depth, 0, index, leafHash).1 ≠ value ⇒ revert`. Supporting closed forms:
  `gate_if_reverts` (the guard-if), `cleanup_bool_evalCall` (`iszero∘iszero`), `abi7396_call`
  (the revert-payload encoder is pure memory + returns 68).
- **Why it matters (spec points 2 and 4):** delivery is accepted ONLY when the submitted Merkle
  proof folds to exactly the authenticated IMT root. Combined with #24 (`foldRoot` purity) this
  reduces "no delivery of a leaf outside the committed tree" to the mathematical statement about
  `foldRoot` preimages — the interpreter is out of the picture. This is the delivered-arm gate of
  the delivered-XOR-reclaimed exclusivity.
- **Caveat / trusted base:** **axiom-free** (`#print axioms` = `[propext, Quot.sound,
  Classical.choice]`) — the revert direction needs only determinism, not keccak injectivity.
  Stated at the gate level (the 4 tail statements as a block, with the operand bindings as lookup
  hypotheses); the decode prelude of `verifyInclusion` (authenticateRoot, calldata decodes,
  commit-value check) is not re-derived. Assumes the `calculateRootMemory` success-path guards; if
  those fail the inner call itself reverts, so no delivery happens on either branch.

### 26. Atomic interop — the reclaim arm's absence witness is a pure fold  ★ NEW  ✅ axiom-clean
`AtomicFlowManager/.../noninclusion_gate_user.lean` *(added 2026-07-11; PR #2218 contracts)*
- **Claim (`verifyNonInclusion_call`):** the WHOLE of `fun_verifyNonInclusion` (success path) has the
  closed form: given a well-formed IMT adjacency window — `lowLeaf.key < value` and
  (`lowLeaf.nextKey = 0` ∨ `value < lowLeaf.nextKey`), both window shapes proven — the function
  returns exactly `eq(foldRoot(proof, index, hashLeaf(lowLeaf)), root)`. The absence witness is
  accepted **iff the adjacency leaf genuinely folds to the authenticated root**. Covers all three
  require-guards, both branches of the conditional window check (`window_body`), and the full
  call wire-up; the `fun_hashLeaf` step is abstracted as a pure-call hypothesis `hhl` (its closed
  form is proven for the byte-identical L2InteropCommitmentTree copy and ports next).
- **Why it matters (spec points 3 and 4):** a reclaim (timeout/refund) is authorized only against a
  *non-inclusion* proof — this theorem reduces that gate to the same pure `foldRoot` as the delivery
  gate (#25). Both arms of delivered-XOR-reclaimed now sit on one mathematical object: exclusivity
  becomes "no leaf can fold to the root both as present (inclusion) and inside an adjacency gap
  (absence)" — an IMT statement, with the interpreter fully discharged.
- **Update (same day):** the `hhl` abstraction is now DISCHARGED — the leaf-hash closed form was
  ported to this tree (`imt_leafhash_user.lean`: `hashLeaf_call_acc`, `finalize_allocation_128_call`,
  `hashLeafOut` + readback/byte-agreement lemmas; the generated bodies differ from the
  L2InteropCommitmentTree copies only in one source-position variable name).
  `verifyNonInclusion_call_concrete` states the end-to-end form with no per-call hypotheses:
  accepted iff `foldRoot(proof, index, hashLeafOut(evm, lowLeaf)) = root`.
- **Caveat / trusted base:** **axiom-free** (`#print axioms` = `[propext, Quot.sound,
  Classical.choice]`, for both the parameterized and concrete forms). Success-path form: the revert
  directions of the three witness guards are not yet stated (each is a small
  `gate_if_reverts`-style corollary if needed).

### 45. Atomic interop — NO DOUBLE DELIVERY: the executed-once core  ★ NEW  ✅ axiom-clean
`InteropHandler/InteropHandler/no_double_delivery_user.lean` *(added 2026-07-12; InteropHandler
newly compiled into the corpus — 632 VC files, `fun_markFullyExecutedAndRun` is a named function)*
- **Claim:** the delivery-side mirror of #22's no-double-refund, over the verbatim compiled
  prologue blocks of `fun_markFullyExecutedAndRun`: the bundle-status slot is one `accOut` step at
  `(bundleHash, 1)` (`mark_slot_block`); the write stores `(old &&& ~255) ||| 2` there
  (`mark_write_block`); the stored word's low byte is exactly `2 = BundleStatus.FullyExecuted` and
  nonzero (`fin_mask_two`); and re-reading the slot the way `fun_getBundleData` does —
  `and(sload(slot), 0xff)` — returns `2` (`delivered_status_reads_two`).
- **Why it matters (spec points 2, 4):** the execute/receive paths process a bundle only when its
  status is `Unreceived` or `Verified`, and `_markFullyExecutedAndRun` sets `FullyExecuted`
  BEFORE running any bundle call (CEI — even a reentrant re-delivery of the same bundle hits the
  already-written status). With this, "paid out at most once" is machine-checked on BOTH sides of
  the bridge: refunds (#22) and deliveries (#45). Together with never-both (#34) and never-neither
  (#35), spec point 4's full shape — exactly one outcome, each side at most once — is covered.
- **Caveat / trusted base:** **axiom-free**. The status-slot equality across calls (the re-check
  recomputes `keccak(bundleHash ‖ 1)` on a later state) is the same `accOut` determinism as #22's
  `check_set_slots_eq`; the status-check comparison itself sits in the dispatcher (same (B)-class
  boundary as `append`), with the check VALUE computed in the named `fun_getBundleData`.

### 44. Atomic interop — FLOW-ID BINDING: the flowId pins the deadline and the clock  ★ NEW  ⚠ uses A6′
`AtomicFlowManager/.../flowid_binding_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim (`flowid_pins_deadline_sl`):** two flow encodings of the compiled shape — the encoder
  writes the masked `deadline` at `headStart+64` and the `settlementLayerChainId` at
  `headStart+96` as its FINAL two writes, and `checkFlowId` keccaks from `headStart` — that hash
  to the SAME flowId carry the same deadline word, the same settlement layer, and the same
  encoding length (hence the same leg count). First concrete instantiation of the pinning
  principle (#43): the static heads are the last writes, so the extraction needs NO reasoning
  about the variable-length leg tails.
- **Why it matters (spec points 3, 4):** closes the loop on the deadline's provenance. The chain
  now reads: the commit value bakes in the flowId (#33) → the gates recompute and match the
  flowId before anything else (#37) → equal flowIds force equal deadlines and clocks (#44) → the
  temporal guards compare against exactly that deadline on exactly that settlement-layer clock
  (#36) → never-both/never-neither (#34/#35). A flow cannot be re-presented with a stretched or
  shortened deadline, a different settlement clock, or a padded leg list: any such variant has a
  different flowId, whose commit values are different leaves entirely (#33).
- **Caveat / trusted base:** A6′ only. The encoder-shape hypothesis (final state =
  `…mstore (h+64) D̂ |>.mstore (h+96) sl`) is read off the compiled encoder verbatim (its last two
  statements); the leg-array heads (offsets 0/32) and tails are not needed for this claim.
- **Update (same day) — the leg-array encoder (`abienc_array_call`):** the inner array encoder's
  closed form — length word at `pos`, `length < 2²⁵¹` guard, element bytes copied to `pos+32`
  (`calldatacopy` kept as the model's opaque state constructor), tail returned as
  `pos + 32·length + 32`. With the outer encoder's head writes this pins the full memory layout
  the flowId hashes. Axiom-free.
- **Update (same day) — the leg-count word (`flowid_pins_legcount`, A6′):** the frame composed:
  the full flow-encode tower reads the first array's LENGTH word back at `h+128` through six
  frame steps — both element copies crossed via the calldatacopy frame (with `calldatacopy`'s
  env-preservation making the calldata-size bounds well-stated). Equal flowIds now pin the
  deadline, the settlement layer, the total encoding length, AND the leg count: a flow cannot
  gain or lose legs under the same flowId at the word level, independently of the total-length
  argument.
- **Update (same day) — the copy frame (`specs/CalldatacopyFrame.lean`):** the deferred induction
  bridge, closed: `lookupMemory_calldatacopy_below` — Clear's `calldatacopy` (a byte-wise
  `updateMemory` fold over extracted calldata) leaves every word STRICTLY BELOW its target
  unchanged, by structural induction on `ByteArray.foldlM.loop`'s countdown argument. Length words
  and heads written before an abi-encode's element copies provably survive them: the pinning
  readbacks (#43/#44) now pass through dynamic-array tails. Axiom-free.

### 43. Keccak PINNING: equal outputs pin the interval, every word, and the LENGTH  ★ NEW  ⚠ uses A6′
`specs/KeccakInjective.lean` *(added 2026-07-12; protocol-wide)*
- **Claim:** the usable contrapositives of A6′, packaged: `keccak256_same_out_interval_eq` (equal
  outputs ⇒ equal preimage byte-intervals), `keccak256_same_out_word_eq` (⇒ every fixed-offset
  word of the two preimages agrees), and `keccak256_same_out_length_eq` (⇒ the preimages have the
  SAME byte length; via the axiom-free `mkInterval_length`).
- **Why it matters (spec points 1, 2, 3):** this is the common core of every dynamic-encoding
  binding in the protocol. The `abi.encode` HEADS — static fields like the flow's `deadline` and
  `settlementLayerChainId`, or the L1 deposit's `originalCaller` — sit at fixed offsets, so they
  are hash-bound by `word_eq` even when the encodings carry variable-length tails; concrete
  instantiations reduce to per-encoder head readbacks (the #28/#33 technique). And `length_eq`
  is the domain-separation backbone: encodings of different byte lengths never hash alike —
  the 97-byte tagged tx-data vs any 96-byte struct hash, the legacy vs new deposit formats
  (`DataEncoding.sol`'s collision comment), the tag word of #33.
- **Caveat / trusted base:** A6′ (`keccak256_inj`) only; `mkInterval_length` is axiom-free.

### 42. Atomic interop — THE CONCRETE INSERT STEP: storage writes to `imtInsert`, end to end  ★ NEW  ✅ axiom-clean
`L2InteropCommitmentTree/.../imt_leaf_storage_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim (`leaves_insert_step`):** under the deployed-contract fact, pairwise triple-separation of
  the grown base set (dischargeable per pair by `leafBase_sep` from key distinctness alone), and
  uniqueness of the low leaf's representation: the insert glue's two struct writes — the retargeted
  low leaf `(sload lowB, ni, v)` at `lowB` and the new leaf `(v, oi, sload (lowB+2))` at `newB`,
  exactly the shapes `read_leaf_call`+`copy_leaf_call` produce — transform the REPRESENTED LEAF SET
  over the grown base set into exactly `imtInsert`, and it remains `GapSound`/`KeyInj`. One
  `Evolution` step, stated directly over the storage model.
- **Why it matters (spec points 1, 4):** this is the insert chain ASSEMBLED. From the compiled
  primitives (#39) through the pointwise effect (#41) and base separation (A6″) into the abstract
  bridge (#40), landing on the `Evolution` step that the temporal theorems consume: every tree
  history built from such steps satisfies never-both (#34) and never-neither (#35). The field
  alignment is definitional — the retarget keeps `sload lowB` (the low leaf's own key) and the new
  leaf inherits `sload (lowB+2)` (the old gap end), matching the Solidity
  `IMTLeaf({value: lowLeaf.value, nextIndex: newIndex, nextValue: _value})` /
  `IMTLeaf({value: _value, ...nextValue: oldNextValue})` verbatim.
- **Caveat / trusted base:** **axiom-free** as stated (separation is a hypothesis here; its
  per-pair discharge uses A6″ `slot_sep`). What remains outside the machine-checked chain is the
  glue SEQUENCING (that the dispatcher calls these primitives in this order with these arguments —
  source-level inspection, documented at #31/(B)) and the guard-derived hypotheses (freshness of
  `v` and the window checks — enforced by the compiled guards per #26/#37 and the insert's own
  reverts).
- **Update (same day) — pointwise histories (`pointwise_history`):** the history theorem
  generalized from the exact two-write tower to `PointwiseStep` — a transition described by its
  REPRESENTED-LEAF effect alone (frame-only for node writes/root publishes/side-array growth, or
  the insert's retarget+append+frame). Same conclusion: all invariants at every snapshot and an
  `Evolution`. This subsumes the GROWTH-variant insert (its extra `sstore`s are leaf-frame-disjoint
  by keccak base separation) and every non-leaf write the contract performs. Axiom-free.
- **Update (same day) — concrete histories are Evolutions (`concrete_history`):** the step was
  upgraded to the fully-inductive form (`leaves_insert_step'`, `RepKeyInj` replacing the
  uniqueness hypothesis and carried forward), and the arc capped: along ANY sequence of
  `ConcreteStep` transitions (identity, or a well-formed insert's two struct writes with
  separated bases) from a sound base, every snapshot keeps `GapSound`/`KeyInj`/`RepKeyInj` and
  the represented sets form an `Evolution` — the abstract never-both (#34) and never-neither
  (#35) theorems apply to the CONCRETE tree with no further hypotheses. Axiom-free.

### 41. Atomic interop — THE INSERT WRITES, pointwise: readback and frame discharged  ★ NEW  ✅ axiom-clean
`L2InteropCommitmentTree/.../imt_leaf_storage_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim:** the general storage round-trip laws of the model — `sload_sstore_self` (re-reading a
  written slot returns the value, ANY value: the zero case erases the key and a missing key reads
  as 0; needs only the deployed-contract fact, preserved across writes by `acct_sstore`) and
  `sload_sstore_ne` (distinct-slot frame, unconditional) — and on top of them
  `insert_writes_readback`: after the insert glue's two struct writes (retargeted low leaf
  `(lv, ni, v)` at `lowB`, new leaf `(v, oi, ov)` at `newB`, the exact shape `copy_leaf_call`
  produces), the represented `AbsLeaf`s are the retarget `⟨lv, v⟩` at `lowB`, the new leaf
  `⟨v, ov⟩` at `newB`, and UNCHANGED at every slot-disjoint base.
- **Why it matters (spec points 1, 4):** these are hypotheses (i)–(iii) of the insert-effect
  bridge (#40), discharged against the real storage model. The remaining concrete inputs to #40
  are now exactly: slot-disjointness of distinct leaf bases (keccak separation, the A6″ family) and
  the uniqueness hypothesis (iv) (from `KeyInj` in context). The chain
  compiled-writes → pointwise effect (#41) → set-level `imtInsert` (#40) → invariants (#30) →
  never-both/never-neither (#34/#35) is complete except for those two arithmetic/context facts and
  the glue sequencing.
- **Caveat / trusted base:** **axiom-free** — in fact only `[propext, Quot.sound]`, not even
  choice. `leafAt` reads fields 0/2 (`value`, `nextValue`); `nextIndex` (field 1) is navigation
  metadata not needed by the safety argument.
- **Update (same day) — keccak base separation (`leafBase_sep`, A6″):** the leaf-slot bases of two
  DISTINCT keys — both computed by the mapping accessor `keccak256(key ‖ base)` over the same base
  word — never collide at any pair of small offsets: `b₁ + i ≠ b₂ + j` for `i, j < 2³²`. The
  interval difference comes from the key word at offset 0 (an `mstore` round-trip through the base
  write), the offset shifting is pure group algebra. With `base_offset_ne` (a triple is internally
  distinct — `[propext, Quot.sound]` only), ALL slot-side hypotheses of the insert chain
  (#40's frame/disjointness, #41's ≠-hypotheses) are now dischargeable from key distinctness
  alone. Axioms: standard three + `keccak256_slot_sep` (the sanctioned A6″ spread idealization).

### 40. Atomic interop — THE INSERT-EFFECT BRIDGE: pointwise writes make `imtInsert`  ★ NEW  ✅ axiom-clean
`specs/IMTAbstract.lean` *(added 2026-07-12; contract-independent)*
- **Claim (`image_insert_effect`):** over any representation function `f : index → AbsLeaf`, if
  going from `f` to `f'` (i) the low index carries the RETARGETED leaf `⟨key, v⟩`, (ii) a fresh
  index carries the NEW leaf `⟨v, nextKey⟩`, (iii) every other index is unchanged, and (iv) the low
  leaf was uniquely represented — then the represented set over the grown index set IS exactly the
  abstract `imtInsert`. And (`image_insert_step`) with a well-formed window and a sound old set,
  the new set is simultaneously `imtInsert` AND `GapSound`/`KeyInj` — one `Evolution` step (#34/#35)
  in a single theorem.
- **Why it matters (spec points 1, 4):** this is the last abstract link in the insert chain. The
  dispatcher glue's storage effect is: read low leaf (`read_leaf_call`), write retargeted low leaf
  and new leaf (`copy_leaf_call` ×2, at `mapping_leaves_call` slots) — #39's verified primitives.
  Discharging (i)–(iv) is now pure slot arithmetic (`sload`-after-`sstore` at keccak-separated
  bases), after which the whole abstract stack — invariant preservation (#30), never-both (#34),
  never-neither (#35) — applies to the concrete tree with no further set theory.
- **Caveat / trusted base:** **axiom-free** (pure Finset algebra). The slot-disjointness needed
  for (iii) concretely is the A6″-family keccak separation the walk machinery already uses.
- **Update (same day) — uniqueness made INDUCTIVE (`image_insert_step'`):** the uniqueness
  hypothesis (iv) is no longer assumed anywhere. `RepKeyInj` (distinct indices represent distinct
  keys) is a fourth invariant PRESERVED by the insert step (`repKeyInj_insert_step` — the retarget
  keeps its key, the new key is fresh), the freshness it needs follows from the gap window itself
  (`fresh_of_window`, via `gap_excludes_member` — no separate guard hypothesis at the abstract
  level), and (iv) is a one-line corollary (`huniq_of_repKeyInj`). The self-contained step
  `image_insert_step'` concludes `imtInsert` + ALL FOUR invariants (`GapSound`/`KeyInj`/
  `RepKeyInj` + the effect) from pointwise writes + window + soundness alone: nothing about the
  insert chain remains non-inductive. Axiom-free.

### 39. Atomic interop — THE LEAVES-MAPPING PRIMITIVES: the insert glue's alphabet  ★ NEW  ✅ axiom-clean
`L2InteropCommitmentTree/.../imt_leaf_storage_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim:** closed forms for the named storage helpers the dispatcher-inlined IMT insert (the (B)
  boundary) sequences over the `leaves` mapping (storage slot 4): `mapping_leaves_call` — the
  accessor `mapping_…_5196(key)` is exactly one `accOut` step at `(key, 4)`, so leaf `i`'s struct
  occupies slots `keccak256(i ‖ 4) + 0/1/2`; and `copy_leaf_call` — the struct write
  `copy_struct_to_storage(slot, ptr)` is exactly three word `sstore`s of the three memory fields
  `(value, nextIndex, nextValue)` at `slot`/`slot+1`/`slot+2` (reads normalized through the
  interleaved `sstore`s via `mload_sstore`).
- **Why it matters (spec points 1, 4):** these are the storage primitives the insert protocol is
  built from — and with the same-day update below, ALL THREE now have closed forms. With them, the leaves-mapping
  abstraction — "`AbsLeaf ⟨value, nextValue⟩` at index `i` lives at `keccak(i ‖ 4)`" — is
  definable against VERIFIED primitives, so the retarget-low-leaf and append-new-leaf writes of
  the insert (#30's `imtInsert`, #34/#35's `Evolution` steps) can be stated as compositions of
  machine-checked pieces; the (B) glue shrinks toward pure sequencing.
- **Caveat / trusted base:** **axiom-free**. The `accOut` slot value is the same keccak-slot atom
  the entire walk machinery uses, so slot non-aliasing facts (A6″ family) apply uniformly.
- **Update (same day) — the struct READ:** `read_leaf_call` — `read_from_storage(slot)` allocates
  a fresh 96-byte struct at the free pointer (`finalize_allocation_96_call`: the fixed-size
  finalizer is exactly `mstore(64, memPtr+96)` under the pointer bound) and copies the three
  storage words from `slot`/`+1`/`+2` into it, returning the pointer (`leafReadEvm`). With all
  three primitives closed, the dispatcher-inlined insert's storage effect is a composition of
  machine-checked pieces end-to-end: read the low leaf, write the retargeted low leaf, write the
  new leaf — at keccak-derived slots the walk machinery already reasons about. Axiom-free.

### 38. Atomic interop — ROOT AUTHENTICATION GUARDS: attested roots, anchored clocks  ★ NEW  ✅ axiom-clean
`AtomicFlowManager/.../authroot_gate_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim:** the two semantic guards of `fun_authenticateRoot` (run by BOTH gates for every proof),
  over their verbatim compiled blocks, both directions:
  `root_verified_pass`/`root_unverified_reverts` — the decoded result of the
  `proveL2MessageInclusionShared` staticcall to the L2 message-verification system contract must
  be TRUE, else `ProofRootNotVerified`; and `multihop_pass`/`final_node_reverts` — a single-level
  / commit-based proof (`finalProofNode = true`), which exposes NO settlement-layer anchor, is
  rejected.
- **Why it matters (spec points 2, 3, 4):** acceptance of `authenticateRoot` means (i) the IMT
  root the fold (#24–#26/#32) runs against really is one the commitment tree PUBLISHED — the
  cross-chain trust anchor, delegated to the message-verification system contract — and (ii) the
  `(slChainId, l1Timestamp)` metadata consumed by the temporal guards (#36) comes from a parsed
  settlement-layer anchor inside that same attested proof: the deadline clock cannot be forged by
  a proof that never touched the settlement layer. Together with #36/#37 this completes the
  guard-level audit of both gates' front doors.
- **Caveat / trusted base:** **axiom-free** as statements about the guard blocks. The staticcall's
  RESULT is a hypothesis (the message-verification system contract is a protocol trust anchor, like
  A1's compiler trust); the metadata-extraction tail (`ProofData` fields via `getProofData`) and the
  failed-staticcall `revert_forward` branch are outside these lemmas.
- **Update (same day) — the decode boundary (`authroot_decode_user.lean`):** a load-bearing MODEL
  fact made explicit: Clear's `staticcall` PRIMOP returns no values (`EVMStaticcall'` = `(s, [])`)
  — external calls are opaque, so the message-verification RESULT is inherently a hypothesis, and
  the #38 guard-level decomposition is the ONLY sound treatment (a success-path closed form of the
  whole function is not expressible in the model). What IS verified around the boundary:
  `validator_bool_pass`/`validator_nonbool_reverts` — the return-data validator accepts exactly
  the boolean words `{0, 1}` and reverts anything else — and `abi_decode_bool_call` — under the
  return-length check, the decoded flag is exactly `mload headStart`, the word the external
  verifier wrote, validated boolean. So #38's `expr_2 ≠ 0` hypothesis is precisely "the verifier
  returned true", with no third value, through a fully machine-checked decode path. Axiom-free.
- **Update (same day) — the prelude alphabet (`authroot_prelims_user.lean`):** seven closed forms
  for the L2Message-construction helpers the function runs before the staticcall — the size-96
  generic finalizer (rounding is the identity), the uint16/address masked memory writers, the
  96-byte allocator, the single-word abi encoder, the PINNED sender constant `0x10012` (the
  commitment-tree address every chain shares — what binds the verified message to the real tree),
  and the address cleaner. All axiom-free; the stitching of #38's guards through the full body is
  now a composition exercise over these plus the encoder/decoder pair around the staticcall.

### 37. Atomic interop — THE FLOW-ID GATE: the flow structure is canonical and bound  ★ NEW  ✅ axiom-clean
`AtomicFlowManager/.../flowid_gate_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim:** the guards of `fun_checkFlowId` — called by BOTH `requireFlowFinalized` (delivery) and
  `authorizeRefund` (reclaim) before any proof is examined — over their verbatim compiled blocks:
  `sorted_pass`/`sorted_reverts` — each adjacent leg-bundle-hash pair must be STRICTLY ascending
  (both directions); `length_match_pass` — `legSourceChainIds` is aligned 1:1 with the bundle
  hashes; `flowid_match_pass`/`flowid_mismatch_reverts` — the declared `flowId` must EQUAL the
  recomputed `keccak256(abi.encode(legBundleHashes, legSourceChainIds, deadline,
  settlementLayerChainId))` (both directions).
- **Why it matters (spec points 1, 2, 3):** the `flowId` is what every leg's commit value bakes in
  (#33). These guards mean an ACCEPTING gate run uses a deadline, leg set, and settlement layer
  that are EXACTLY the ones bound into every tree commitment: a tampered deadline (to force or
  block a timeout), an injected or duplicated leg, a permuted flow re-presentation, or a swapped
  settlement-layer clock is rejected up front — before any Merkle proof is even looked at.
  Canonical ascending order also makes the flow presentation unique per leg set.
- **Caveat / trusted base:** **axiom-free**. The length guard's revert direction is not stated
  (its revert body calls the calldata-tail accessor whose closed form is not yet proven); the pass
  direction is what acceptance-implies arguments need. Injectivity of the flow encoding (flowId ⇒
  unique legs/deadline/sl, the #33-style A6′ companion) needs the dynamic-array encoder's closed
  form — future work.

### 36. Atomic interop — THE TIMEOUT GATE'S TEMPORAL GUARDS: acceptance pins the deadline window  ★ NEW  ✅ axiom-clean
`AtomicFlowManager/.../timeout_gate_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim:** the three temporal guards of `fun_verifyTimeoutAdjacency` (the reclaim gate's outer
  verifier), each proven in BOTH directions over its exact statement block quoted verbatim from the
  compiled body: the absence-batch guard falls through iff `tN ≤ D̂` and reverts otherwise
  (`absence_ontime_pass`/`absence_late_reverts`); the successor guard iff `D̂ < tS`
  (`successor_late_pass`/`successor_ontime_reverts`); the adjacency guard iff `bS = bN + 1`
  (`adjacency_consecutive_pass`/`adjacency_gap_reverts`). Supporting: `abi64_call` — the closed
  form of `abi_encode_uint256_uint64` (the temporal reverts' error encoder).
- **Why it matters (spec points 3, 4):** any ACCEPTING run of the timeout gate satisfies
  `tN ≤ D̂ < tS` with consecutive batches — precisely the successor-pinning premises of the
  abstract never-both theorem (#34, `delivered_and_reclaimed_impossible`): batch `N` is the LAST
  on-time snapshot, so absence there (checked against the same root by #26's `verifyNonInclusion`)
  is absence that delivery evidence cannot coexist with. The delivery side's `t ≤ D` premise is
  guarded symmetrically by `verifyInclusion`'s deadline check (same `if gt(t, deadline) revert`
  shape). The revert directions also close the force-refund-off-stale-root attack concretely: an
  in-time successor (`tS ≤ D̂`) or a non-consecutive pair is REJECTED, not merely not-accepted.
- **Caveat / trusted base:** **axiom-free** (all six theorems + encoder = standard three). The
  guards are stated over their verbatim statement blocks with variable-lookup hypotheses; stitching
  them through the full `fun_verifyTimeoutAdjacency` body (through `authenticateRoot`'s closed
  form) is the remaining composition step.
- **Update (same day) — the DELIVERY side:** `fun_verifyInclusion`'s two guards, same both-ways
  treatment: `delivery_ontime_pass`/`delivery_late_reverts` — the membership batch guard falls
  through iff `t ≤ D̂` (the uint64-masked deadline; #34's delivery-side premise — a commit cannot
  be back-dated past the deadline), and `value_match_pass`/`value_mismatch_reverts` — the proof's
  leaf field 0 must EQUAL the leg's commit value (the concrete hook for #33's binding: no
  substitution of what is being delivered). Both axiom-free. All four temporal guards of the two
  gates are now verified in both directions.

### 35. Atomic interop — RECLAIM LIVENESS: a gap witness always exists for an absent leg  ★ NEW  ✅ axiom-clean
`specs/IMTAbstract.lean` *(added 2026-07-12; contract-independent)*
- **Claim (`reclaim_witness_available`):** along any IMT history (`Evolution`) from a sound base
  containing the zero leaf, EVERY absent nonzero commit value has a valid gap witness at EVERY
  snapshot — a leaf whose window straddles it, exactly what the reclaim gate (#26) requires.
  Supporting: two further linked-list invariants — `NextClosed` (every nonzero `nextKey` resolves
  to a real leaf; no dangling links) and `WindowPos` (windows open upward) — each preserved by the
  guarded insert (`imtInsert_nextClosed`/`imtInsert_windowPos`); the full four-part `SoundState`
  bundle is inductive (`evolution_sound`, genesis singleton proven sound); and
  `gap_witness_exists` — in a well-formed list, the MAXIMAL key below an absent `v` carries a
  straddling window (its link target is a real leaf, which would beat maximality if it were below
  `v`, and equals `v` never since `v` is absent).
- **Why it matters (spec points 3, 4):** this is the availability half of "reclaim on failure —
  at any time" and the "never neither" side of exactly-one-outcome, abstractly: a leg that was
  never committed can ALWAYS be witnessed absent — no tree state, however grown, can strand a
  depositor by making the reclaim proof impossible. Dual to #34 ("never both"): together they pin
  the abstract outcome space to exactly one of delivered/reclaimed, given the gates' evidence
  shapes.
- **Caveat / trusted base:** **axiom-free** (pure order theory). Liveness here means witness
  EXISTENCE; producing the witness (indexing into the tree) and the gate accepting it are the
  concrete layers #24–#26/#32. The absent-forever hypothesis (`v ∉ keys (S j)`) is the
  "transaction failed / leg never committed" premise.

### 35b. Atomic interop — RECLAIMABILITY PINS ABSENCE: the sharp iff  ★ NEW (2026-07-17)  ✅ axiom-clean
`specs/IMTAbstract.lean` *(contract-independent)*
- **Claim (`reclaimable_iff_absent`):** along any evolution from a sound base with the zero leaf, a
  nonzero commit value `v` has a valid reclaim witness at snapshot `j` **if and only if** `v ∉ keys
  (S j)`. The forward (⇐) direction is reclaim liveness (#35); the new backward (⇒) direction is
  `present_not_reclaimable` — if `v` IS a key of a `GapSound` snapshot (the leg was delivered, its
  leaf is in the tree) then NO leaf carries a window straddling `v`, so the reclaim gate's witness
  precondition (#26) is *unsatisfiable*. The converse needs only `GapSound` — no timestamps, no
  evolution — a direct consequence of `gap_excludes_member`.
- **Why it matters (spec point 4):** sharpens exactly-one-outcome from "never both / never neither"
  (#34/#35, which bound the outcomes) to an *equivalence*: the reclaim gate fires on **exactly** the
  legs the tree never delivered — no false refunds (a delivered leg can never also be refunded, the
  anti-double-spend guarantee on the reclaim side), and no missed refunds (an undelivered leg is
  always witnessable). Together with #34 this closes the abstract outcome dichotomy on the nose.
- **Caveat / trusted base:** **axiom-free** — `#print axioms` shows only `propext`, `Quot.sound`,
  `Classical.choice`; no keccak axioms (A6′/A6″), no `sorry`. Reclaimability here is witness
  existence; the concrete gate accepting the witness is #26/#32.

### 34. Atomic interop — DELIVERED XOR RECLAIMED, temporal core: never both  ★ NEW  ✅ axiom-clean
`specs/IMTAbstract.lean` *(added 2026-07-12; contract-independent)*
- **Claim (`delivered_and_reclaimed_impossible`):** fix an IMT history — an `Evolution`: each
  snapshot is the previous one or a guarded `imtInsert` (fresh key through a well-formed window,
  exactly the tree contract's operation) from a `GapSound`/`KeyInj` base — with monotone settlement
  timestamps `t` and a deadline `D`. Then **delivery evidence** for a commit value `v` (membership
  in some snapshot settled on time, `t i ≤ D` — what gate #25 demands of every leg) and **reclaim
  evidence** for the same `v` (a gap witness straddling `v` in the last on-time snapshot, pinned by
  a successor `D < t (j+1)` — what gate #26 demands of the missing leg) CANNOT coexist. Supporting:
  `imtInsert_keys_grow` (the insert never removes a key — the erased low leaf returns retargeted,
  so key sets only grow), `evolution_keys_mono`, and `evolution_invariant` — `GapSound`/`KeyInj`
  are INDUCTIVE along any evolution (the induction #30 promised, now formal), with the genesis
  singleton `{⟨0,0⟩}` and the empty base both proven sound.
- **Why it matters (spec point 4):** this is "never both", the heart of exactly-one-outcome, at
  the abstract level: on-time membership persists to the pinned snapshot (timestamps monotone force
  `i ≤ j`; keys only grow), where the gap witness excludes it. Combined with the concrete layers —
  the gates reduce to `foldRoot` (#24–#26), the root pins the leaf (#27/#28/#32), the leaf pins the
  leg (#33), and the builder implements guarded inserts (#31 + source-level (B)) — the bridge's
  central safety property is closed end-to-end modulo the documented (B) glue.
- **Caveat / trusted base:** **axiom-free** (pure order theory; standard three only). The
  "append-only + monotone timestamps" hypotheses are protocol facts about settled batches (each
  root is the predecessor plus inserts; `l1Timestamp` is monotone), matching the source docstring's
  argument verbatim.

### 33. Atomic interop — COMMIT-VALUE BINDING: the tree leaf value pins the flow leg  ★ NEW  ⚠ uses A6′
`AtomicFlowManager/.../commit_binding_user.lean` *(added 2026-07-12; PR #2218 contracts)*
- **Claim:** (i) `commitValue_call_acc` — `fun_commitValue(flowId, specHash)` is the pure
  `commitValueOut`: a keccak over the 3-word scratch `TAG ‖ flowId ‖ specHash` written at the free
  pointer (domain tag `ATOMIC_COMMIT_LEAF_TAG = shl(226, 0x0d114153)`), proven chunk-wise over the
  three generated body blocks with the length word round-tripped (`mload(P) = 96`). Axiom-free.
  (ii) `commitValueOut_inj` (A6′) — two collision-free commit values that are EQUAL carry the same
  `flowId` AND the same `specHash` (bundle hash), extracted from the keccak preimage at region
  offsets 32/64.
- **Why it matters (spec points 1, 2, 3):** the commit value is the ONLY thing the interop
  commitment tree stores per flow leg — `append` inserts it on deposit, `requireFlowFinalized`
  proves its membership for delivery, `authorizeRefund` proves its absence for reclaim. Injectivity
  closes the last identification link: root —(#27)→ leaf hash —(#28)→ leaf fields —(#33)→
  `(flowId, bundleHash)`. A membership proof or absence witness for one leg can never be repurposed
  for another flow or another bundle; the deposit-side claim (point 1) and the delivery/reclaim
  gates (points 2–3) all speak about the SAME uniquely-identified leg. The domain tag also
  separates commit leaves from every other keccak-encoding domain in the protocol.
- **Caveat / trusted base:** closed form **axiom-free**; injectivity **A6′** (standard three +
  `keccak256_inj`). The dispatcher glue calling `commitValue` from `append`/the gates is the same
  (B)-boundary as #31's insert protocol (named functions verified; dispatcher inlining by source
  inspection).

### 32. Atomic interop — THE VERIFIER FOLD REPLAYS THE BUILDER WALK  ★ NEW  ✅ axiom-clean
`L2InteropCommitmentTree/.../imt_replay_user.lean` *(added 2026-07-11; PR #2218 contracts)*
- **Claim (`fold_replays_walk`):** let the builder walk (`updateWalk`, #31) run `k` collision-free
  levels from leaf `cur` at position `idx`, storing a final root. Then ANY verifier evm that (i)
  carries the walk's final keccak cache, (ii) agrees with the walk's initial memory on the scratch
  junk window `[64, 95)`, and (iii) is given a path array holding exactly the siblings the walk
  read, folds (`foldRoot`, #24 — the delivery/reclaim gates' verifier) the SAME leaf at the SAME
  position to EXACTLY the stored root. The three hypotheses of the agreement induction
  (`fold_walk_agree`, arc A) are DISCHARGED, not assumed: `walk_caches` — a collision-free walk
  cached every level's pair hash itself (`accOut_caches_of_clean` at the step, cache monotonicity
  to the final state); `updateWalk_junk`/`walkPreHash_junk` — the walk writes memory only in
  scratch `[0, 64)`, so the junk window is invariant; `foldWalk_mload_high`/`foldWalk_index` — the
  fold's path reads (at `≥ 96`) see its initial memory and its counter is `iv + j`.
- **Why it matters (spec points 2, 3, 4):** this closes arc (A) end-to-end at the concrete layer:
  the root the builder stores is not merely *some* commitment — the gates' own fold procedure,
  replayed with the builder's witnesses, RECOVERS that root from the written leaf. Composed with
  #27 (`foldRoot_binding`: same root + same position ⇒ same leaf), the stored root verifies the
  written leaf and ONLY the written leaf at its position. What delivery/reclaim check is exactly
  what the builder committed.
- **Caveat / trusted base:** **axiom-free** (`#print axioms fold_replays_walk` = standard three;
  no A6′/A6″, no `sorryAx`). The sibling-array hypothesis (`hsibs`) is the prover-supplies-the-
  right-path premise — substituting wrong siblings changes the fold output, which #27 then rejects.
- **Update (same day) — the composition capstone (`root_pins_written_leaf`, A6′):** the replay
  fold also STAYS collision-free (`fold_replays_walk_clean` — every level is a cache hit, so the
  fold carries the verifier's own flag; proven by extending `fold_walk_agree` with a
  flag-preservation conjunct, axiom-free). Composing with #27's `foldRoot_binding`: if the builder
  stored root `R` for leaf `cur` at position `idx`, then ANY collision-free fold of ANY leaf `L`
  at position `idx` reaching `R` — arbitrary proof array, memory, level counter — forces
  `L = cur`. The committed root admits EXACTLY the written leaf at its position: uniqueness of
  what the delivery (#25) and reclaim (#26) gates can ever accept, stated against the builder's
  own write. Axioms: standard three + `keccak256_inj` (A6′) only.

### 31. Atomic interop — THE TREE-BUILDER'S MERKLE UPDATE LOOP IS A PURE WALK  ★ NEW  ✅ axiom-clean
`L2InteropCommitmentTree/.../imt_storage_atoms_user.lean`, `imt_update_fold_user.lean`
*(added 2026-07-11; PR #2218 contracts)*
- **Claim (`update_loop`):** `fun_updateLeaf`'s storage-side Merkle update loop equals the pure
  iteration `updateWalk` of per-level steps `stepOdd`/`stepEven`/`stepEdge` — each: read the
  sibling (2-level dynamic storage array via keccak slots / the side array at the tree edge), hash
  the pair (`accOut`), store the parent at level `i+1`, halve the indices; then break at the level
  count. Proven by induction with all three body variants (`updateBody_odd/even/edge`), the break
  pass, and checkpoint pass-through. Under it: 7 storage atoms (array accessor `keccak(slot)+i`,
  masked update = plain `sstore`, extractor = id, `mod2/div2/±1`) and 5 block closed forms.
- **Hypotheses (the honest remaining obligations):** per-level array bounds (`PassOK` over walk
  prefixes — tree well-formedness) and level-count slot stability (`hwalk_ss` — the parent stores
  at `keccak(…)+j` never hit the low length slot; dischargeable from A6″ `keccak256_ne_lowSlot`).
- **Update (same day) — U4 DONE:** `updateLeaf_call` gives the FULL closed form of
  `fun_updateLeaf`: range guard, leaf write (`leafWriteEvm` — the new leaf hash stored at
  position `idx` of level 0), the `updateWalk` recompute, and the new root returned — axiom-free.
- **Update (same day) — `pushNewLeaf` DONE (non-growth path):** `pushNewLeaf_call` gives the full
  closed form of the append path: count bump, capacity check (growth branch skipped; its three
  chunks `growA/B/C_block` are separately proven for the growth variant), frontier padding
  (`pad_loop`/`pad_if` = the pure `padWalk`, dual-exit induction with key preservation), and the
  root recompute DELEGATING to the proven `updateLeaf_call`. Axiom-free.
- **Why it matters (spec point 4):** this is the concrete half of the tree-builder arc. Both
  mutating entry points are now pure functions; the roots the contract publishes are `updateWalk`
  images — the bridge to showing published roots commit
  only `GapSound` leaf sets (#30), which discharges the exclusivity capstone's one hypothesis.
- **Caveat / trusted base:** axiom-free (`#print axioms update_loop` = standard three, no
  `sorryAx`, no keccak axioms).
- **Update (same day) — the discharge layer:** the walks' slot-stability packs are DISCHARGED
  (`imt_walk_discharge_user.lean`): memory writes and keccak steps provably never touch storage
  (frame lemmas over the model), and every per-level store lands at `keccak(…)+j` which misses all
  reserved low slots by the A6″ spread axiom (`keccak256_add_ne_lowSlot`, added to the sanctioned
  family). `updateWalk_sload_low` + `padWalk_sload_low`: both builder walks preserve every low
  slot, given only collision-freeness flags and `2³²` offset bounds.
- **The remaining distance to the capstone (delivered-XOR-reclaimed), precisely:** the capstone
  (#29 file) needs "committed leaves abstract into a `GapSound` set". With the builder now fully
  closed-form, this decomposes into exactly two obligations:
  **(A) builder–verifier agreement — DONE, instantiated** (`imt_agreement_user.lean` +
  `imt_replay_user.lean`, both axiom-free): `fold_walk_agree` — if, level by level, the verifier
  fold reads the walk's sibling, the walk's pair-hash cache entry is transported into the verifier
  evm, and the two memories agree on the scratch junk window `[64, 95)`, then the fold REPRODUCES
  the walk's node chain. #32 (`fold_replays_walk`) then DISCHARGES all three per-level premises
  concretely (the collision-free walk caches its own hashes; the walk never writes `[64, 95)`; the
  fold's path reads see its initial memory) — so the closed form is: cache transport + junk
  agreement + the walk's siblings in the path array ⇒ `foldRoot` = the stored walk root.
  **(B) the insert protocol** *(present in the compiled Yul, but not in the generated corpus)*:
  the composition `updateLeaf(lowIdx, hashLeaf(retargetedLow)); pushNewLeaf(hashLeaf(newLeaf))` is
  `IndexedMerkleTree.sol::insert` (era-contracts, lines 60–105) — verbatim the abstract
  `imtInsert` of #30 (guards: `value ≠ 0`, fresh `valueToIndex`, low-leaf window
  `lowLeaf.value < value {< lowLeaf.nextValue or nextValue = 0}`; then retarget + append). It IS
  compiled into `yul/L2InteropCommitmentTree.yul` — inlined in the external-function dispatcher
  (guards at src offsets 2724–3011, the bounded low-leaf search loop, the two struct stores, and
  the calls `fun_updateLeaf_5202(lowLeafIndex, fun_hashLeaf(...))` /
  `fun_pushNewLeaf(fun_hashLeaf(...))` / `fun_publishRoot(newRoot)` at Yul lines ~120–250). The VC
  generator, however, extracts only NAMED functions, so this dispatcher glue has no generated Lean
  and cannot get a machine-checked closed form under the current pipeline. (B) therefore remains
  the one code-level hypothesis, but it is now pinned to ~60 lines of straight-line, source-mapped
  dispatcher glue whose shape is `imtInsert` by direct inspection. Under (B), #30's
  `imtInsert_gapSound` gives the invariant by induction from the empty tree, and with (A) + #32 +
  #27/#28 the capstone's `habs` hypothesis is satisfied — completing spec point 4.

### 30. Atomic interop — ABSTRACT IMT INVARIANT: gap soundness, exclusion, and insert preservation  ★ NEW  ✅ axiom-clean
`specs/IMTAbstract.lean` *(added 2026-07-11; contract-independent)*
- **Definitions:** `GapSound s` — every leaf's `nextKey` is a sound gap witness (any strictly larger
  key in the set is ≥ `nextKey`, and one existing forces `nextKey ≠ 0`); `KeyInj s` — keys identify
  leaves; `imtInsert s W₀ v` — the IMT insert (retarget the low leaf's `nextKey` to `v`, add
  `⟨v, W₀.nextKey⟩`).
- **Claims:** (i) `gap_excludes_member` — in a `GapSound` set, an adjacency window straddling `v`
  excludes ANY member with key `v` — the CROSS-position exclusivity, abstractly; (ii)
  `imtInsert_gapSound` + `imtInsert_keyInj` — the insert operation PRESERVES both invariants for a
  fresh key through a well-formed window. With the trivial empty-tree base case, every tree
  reachable by inserts is `GapSound` by induction.
- **Why it matters (spec point 4):** this is the missing mathematical half of
  delivered-XOR-reclaimed. #29 closed the same-position case unconditionally; #30 closes the
  cross-position case GIVEN the invariant, and shows the invariant is inductive under exactly the
  operation the tree-builder performs. The remaining obligation is now purely mechanical: the
  concrete `L2InteropCommitmentTree` insert path implements `imtInsert` (its low-leaf window check
  is #26's adjacency condition verbatim), connecting the committed roots to `GapSound` sets.
- **Caveat / trusted base:** **axiom-free** (pure order theory; `#print axioms` = standard only,
  no A6′, no EVM semantics).

### 29. Atomic interop — SAME-POSITION EXCLUSIVITY: member and gap cannot share a slot  ★ NEW  ⚠ uses A6′
`AtomicFlowManager/.../exclusivity_user.lean` *(added 2026-07-11; PR #2218 contracts)*
- **Claim (`same_position_member_gap_impossible`):** an inclusion leaf `L` with `L.key = value`
  (what the delivery gate #25 requires) and an adjacency leaf `W` with `W.key < value` (what the
  reclaim gate #26 requires) cannot BOTH fold to the same root at the same tree position — the
  binding chain (#27 root→hash, #28 hash→fields) forces `W.key = L.key = value`, contradicting the
  strict window edge. Fully composed from the two binding theorems; no execution hypotheses beyond
  collision-freeness and a sane free pointer.
- **Why it matters (spec point 4):** this is the first slice of delivered-XOR-reclaimed proper. Per
  position, the root admits at most one leaf (#27/#28), and that leaf cannot simultaneously be the
  delivered member and the reclaim witness (#29). The REMAINING obligation is now precisely scoped:
  the cross-position case — a member of `value` at position `i` and a gap straddling `value` at
  position `j ≠ i` — which is excluded exactly by the IMT linked-list sortedness invariant that the
  tree-builder (`L2InteropCommitmentTree` insert path) maintains. That invariant is the next arc.
- **Caveat / trusted base:** **A6′** (standard three + `keccak256_inj`, no `sorryAx`).
- **Update (same day) — conditional capstone:** `committed_member_gap_impossible` +
  `CommittedLeafAt` state the FULL exclusivity in one theorem: if all leaves committed under root
  `R` (the exact evidence shape gates #25/#26 produce — collision-free hash + fold reaching `R`)
  abstract into some `GapSound` set (#30), then a delivery witness for `value` and a reclaim
  window straddling `value` cannot coexist at ANY pair of positions. The theorem itself is
  axiom-free — every remaining obligation of spec point 4 is now the single hypothesis "the
  tree-builder's roots commit only `GapSound` leaf sets" (`habs`/`hS`), to be discharged by
  verifying the `L2InteropCommitmentTree` insert path against `imtInsert` (#30 shows that
  operation preserves the invariant).

### 28. Atomic interop — LEAF-HASH BINDING: the leaf hash pins the leaf fields  ★ NEW  ⚠ uses A6′
`AtomicFlowManager/.../leafhash_binding_user.lean` *(added 2026-07-11; PR #2218 contracts)*
- **Claim (`hashLeafOut_inj`):** two collision-free `hashLeafOut` computations with the same hash
  output agree on all three IMT leaf fields `(key, nextIndex, nextKey)` — extracted from the keccak
  preimage at region offsets 0/32/64 via memory read-back through the five scratch writes
  (`leafScratch_field0/1/2`) and symbolic `mkInterval` element extraction.
- **Why it matters (spec points 2, 3, 4):** completes the commitment chain
  root —(#27)→ leaf hash —(#28)→ decoded fields. For a committed root, a proven tree position now
  determines the actual VALUES the gates read: #25's commit-value check (field 0) and #26's
  adjacency window (fields 0 and 2). The delivered value and the witnessed gap are unique per
  position — no substitution at any layer of the proof.
- **Caveat / trusted base:** **A6′** (`#print axioms` = standard three + `keccak256_inj`, no
  `sorryAx`). Hypotheses: collision-free end states and a sane free pointer (`96 ≤ P`,
  `P + 128 ≤ 2⁶⁴−1` — Solidity's allocator guarantees both).

### 27. Atomic interop — MERKLE PATH BINDING: the committed root pins every position  ★ NEW  ⚠ uses A6′
`AtomicFlowManager/.../merkle_binding_user.lean` *(added 2026-07-11; PR #2218 contracts)*
- **Claim (`foldRoot_binding`):** two collision-free `foldRoot` computations at the SAME index that
  reach the SAME root carry the SAME leaf — the proof arrays, memory states and level counters may
  all differ; only index and root are shared. Supporting results: `accOut_inj` (the pair hash
  `keccak(a‖b)` pins BOTH children — equal outputs force equal 64-byte preimages, extracted at
  words 0 and 32), and `foldRoot_clean_backward` (the collision flag is monotone through the fold,
  so end-state cleanliness certifies every step).
- **Why it matters (spec points 2 and 4):** with #24–#26 the two verification gates are pure
  `foldRoot` statements; this theorem makes the committed root a BINDING commitment: each tree
  position holds exactly one leaf value, so a delivery cannot smuggle a substituted leaf through a
  valid-looking proof at the same position. It is the per-position half of delivered-XOR-reclaimed;
  the remaining cross-position half (an inclusion leaf for `value` vs an adjacency window
  straddling `value` cannot coexist in one root) sits on top of this plus the IMT sortedness
  invariant of the tree-builder.
- **Caveat / trusted base:** uses **A6′** (`#print axioms` = `[propext, Quot.sound,
  Classical.choice, keccak256_inj]`, no `sorryAx`) — collision resistance idealized as injectivity,
  the standard assumption for Merkle binding. Cleanliness (no recorded hash collision in the final
  evm) is a hypothesis, discharged in practice by the model's collision flag staying `false`.

---


## Part B addendum — 2026-07-22 session (groups #46–#54)

All statements below are axiom-free (standard `propext/Quot.sound/Classical.choice` base only)
unless noted; every file compiles green. Corpora: `specs/IMTAbstract.lean`, `specs/KDParallel/`,
`specs/InteropHandler/` (pre-relocation compile), `specs/L2InteropHandler/` (PR #2303 relocated
compile, 614 VCs), `specs/L2AssetRouter/` (624 VCs).

- **#46 Delivered-value ledger + exactly-once (abstract).** `IMTAbstract.lean`:
  `evolution_keys_ledger` (keys at step n = genesis ∪ per-step increments), `evolution_card_ledger`
  (tree size = genesis + effective inserts), `evolution_key_origin_exists_unique` (∃! entry step),
  `evolution_insert_unique` (the guarded insert never runs twice for one value).
- **#47 n-step fold agreement (abstract).** `KDParallel/FoldAgreement.lean`: `accFold` (dependent
  accessor chain — per-level `(key, base)` a function of the running hash; covers nested-mapping
  chains and Merkle pair-hash folds), `accFold_agree` (junk-window frame + honest per-level cache
  entries force the cross-evm fold to the honest value at any depth), `accFold_deterministic`
  (honest-clean + cache transport pins the cross fold), plus n-step junk-window/cache-mono/
  clean-backward/caches-of-clean frames.
- **#48 Executor binding completed (old InteropHandler corpus).** `exec_allowed_user.lean`:
  `auth_executor_pass` — the designated executor (chain-exact or chain-agnostic, 160-bit-masked
  address = caller) passes the authorization; with `auth_self_pass` the accepting surface of the
  intended-executor binding is closed.
- **#49 L2InteropHandler corpus + executor-binding port.** Upstream moved InteropHandler verbatim
  into `interop-handler/` (Base + L1/L2 split); recompiled, regenerated, mcopy ported.
  `exec_allowed_user.lean` (new corpus): `auth_self_pass` + `auth_executor_pass` over the
  dispatcher-inlined auth block. *Caveat: dispatcher glue is not generator-extracted; the quoted
  block is source-verbatim.*
- **#50 No-double-delivery, end to end (new corpus).** `no_double_delivery_user.lean`:
  mark slot/write closed forms (accOut(bh,1), `(old&&&~255)|||2`), 3-way status guard,
  `require_bap_pass/reverts`, `status_read_block` (fun_getBundleData's masked-sload tail),
  `read_after_mark_two` (cross-evm re-read = 2 via `accOut_deterministic` + storage frame),
  `no_double_delivery_reverts` (guard 0 ⇒ BundleAlreadyProcessed revert). *Caveats: call-boundary
  argument passing and status-slot preservation between mark and re-read are explicit hypotheses.*
- **#51 Bundle provenance + attestation (new corpus).** `verify_bundle_gate_user.lean`:
  `verify_sender_pass/reverts` (the inclusion proof's masked `message.sender` must be the
  InteropCenter built-in `0x1000D`, else InvalidSender), `inclusion_verified_pass/
  inclusion_unverified_reverts` (the `proveL2MessageInclusionShared` verdict — trust anchor pinned
  at built-in `0x10009` — must be true, else MessageVerificationFailed), `call_failure_forwards`
  (a failed attestation call always reverts, both returndatacopy branches). *Caveat: the staticcall
  itself is the model's opaque external-call boundary (#38-style decomposition).*
- **#52 executeCalls guard surface (new corpus).** `exec_calls_gate_user.lean`:
  `call_version_pass/reverts` (every dispatched call carries INTEROP_CALL_VERSION = 1),
  `bth_addr_mask` + `holder_code_pass/reverts` (call value is sourced only from the pinned
  base-token holder `0x10011`; codeless holder reverts), `fail_forward_reverts` (generic
  external-call failure arm, identifier-parametric, rfl-checked against the verbatim quotes) with
  instances `give_call_failure_forwards` (unfunded ⇒ revert) and `dispatch_call_failure_forwards`
  (any failed receiveMessage ⇒ whole delivery reverts — all-or-nothing DELIVERY on the
  executing chain; distinct from the AtomicFlow's cross-chain atomicity, i.e. executed on one
  chain ⇒ executable on all chains, which lives at the AtomicFlowManager layer).
- **#53 executeCalls loop, base case.** `executeCalls_empty` — full-function closed form: an empty
  bundle returns with caller store and evm untouched (`execCall` in = `Ok evm store` out);
  `index_access_call` — the in-bounds element address closed form (first step-case dependency).
  *Remaining: the loop step case (oracle packs for the two opaque call results per iteration).*
- **#54 L2AssetRouter recovery gate, exact both ways.** `recover_gate_user.lean`:
  `afm_addr_mask` + `only_afm_recovers` (only the AtomicFlowManager built-in `0x10014` may invoke
  the timeout recovery; anyone else gets Unauthorized), `recover_short_returns_false` +
  `recover_wrong_selector_returns_false` (degenerate/foreign payloads return false with the evm
  untouched — no decode, no NTV call), `slice4_call`/`bytes4_call` (calldata helper closed forms;
  the calldataload word stays symbolic per A2a), `recover_selector_match_continues` (liveness: a
  correct finalizeDeposit payload is NOT blocked). *Caveat: the NTV forward is the opaque
  external-call boundary; the calldata-content selector value is symbolic (A2a model bug bars
  byte-content claims).*
- **#55 executeCalls loop, STEP CASE — the pre-dispatch closed form (2026-07-23).**
  `exec_calls_gate_user.lean`: eight chunk arms over a generic store — `stepChunk1_arm` (element
  address `arr + 32·i + 32` via `index_access_call`), `stepChunk2_arm` (version acceptance ⇒ test
  value 1), `stepTarget_arm` (**dispatch target = `mload(_mpos+64) &&& (2^160−1)`**, the masked
  `interopCall.to`), `stepStaging_arm` (bundle hash staged at `freshPtr+32`), `stepCommit_arm`
  (**`expr = keccak(bundleHash ‖ i)`** under a known-hash hypothesis; `keccak_prim` collapses the
  primop match), `stepSender_arm` (source word = `mload(_mpos+96) &&& mask`), `stepFormat_arm`
  (composes `formatEvmV1_small_call`), `stepEncode_arm` (selector + `abi_encode3_call` payload +
  calldata length); then the two-stage join `executeCalls_step_guards` (both guards skipped for a
  version-1, zero-value call; the value-transfer sub-block never evaluated) and
  **`executeCalls_step_prefix`** — the oracle-pack lemma: the whole loop body is deterministic up
  to the dispatch-call boundary, 36-insert store tower, generic in the remaining statements (the
  `cons` peel is constant-fuel and tail-generic). Every observable of a dispatched call is pinned
  before the boundary: version, target, value (0-class), commitment, formatted source, payload.
  *Caveats: zero-value + small-chain-id class; keccak result and the finalize/probe memory
  readbacks are explicit hypotheses (the oracle pack); the dispatch call itself is the #38
  boundary.*
- **#56 executeCalls loop ABSTRACTION PIPELINE, sorry-free (2026-07-23).**  The Clear
  reasoning-principle route for the dispatch loop is now fully machine-checked:
  `for_7291460318072256587_abs_of_code` (exec of the For ⇒ `Spec AFor`) depends only on the
  standard axiom trio.  All 65 scaffold templates in the cone (34 blocks, 21 ifs, 2 switches,
  8 callee functions) plus the loop template itself were filled with the LOSSLESS pass-through
  idiom `A_X := X_concrete_of_code.1` — the abstract spec IS the concrete spec, so #55's
  `executeCalls_body_prefix` applies to `ABody` directly.  `ACond = fromBool (var_i < length)`
  is driven exactly.  Filled by four parallel subagents against AtomicFlowManager/L2ICT
  exemplars, verified file-by-file.  `A_fun_executeCalls` is likewise
  lossless and `fun_executeCalls_abs_of_code` (execCall ⇒ Spec) is axiom-clean — the
  whole-function pipeline is structurally complete.  `AFor` is now the FREE
  loop invariant — an inductive iteration transcript whose constructors are the five
  reasoning-principle obligations (nested `Spec` recursion split into per-`State` fields for
  kernel positivity).  Nothing in the pipeline is a scaffold: `ACond` exact, `ABody`/`APost`
  lossless, `AFor` free — per-call consequences are derivable by induction on the transcript,
  with #55's `executeCalls_body_prefix` applying to each `ABody` step.*
- **#57 VERIFIED ⇒ EXECUTABLE — the status machine closed both ways (2026-07-23).**
  `verify_mark_user.lean`: the Verified-status mark closed forms (slot = `accOut(bundleHash,1)`,
  write `(old &&& ~255) ||| 1`, `BundleVerified` log2 state-transparent, masked re-read = 1,
  `read_after_verify_one` cross-evm transport), and the end composite
  `verified_bundle_executable` — verifyBundle's mark makes executeBundle's status guard PASS
  (`statusGuard` publicized in `no_double_delivery_user.lean`).  With #50 (executed ⇒ marked 2 ⇒
  re-delivery reverts), both halves of the bundle status machine are machine-checked.
  *Caveats: same transport-frame hypotheses as #50 (junk window, cache monotonicity,
  cleanliness, no intervening slot write).*
- **#58 THE ENTIRE L2InteropHandler ABSTRACTION LAYER, sorry-free (2026-07-23).**  Following
  #56's method at corpus scale: all 241 remaining scaffold templates (blocks, ifs, switches,
  six more for-loops with exactly-driven conditions, abi codecs, require helpers, and the
  function-level specs) filled with the lossless pass-through idiom by six parallel subagents
  plus two reconciliation sweeps, each file verified individually; 206 + 260 never-built
  generated modules compiled to unblock the cones.  Result: `<fn>_abs_of_code`
  (`execCall ⇒ Spec A_<fn>`) is axiom-clean for EVERY function in the contract —
  `fun_executeCalls`, `fun_verifyBundle`, `fun_getBundleData`, `fun_tryParseV1`,
  `fun_tryParseV1Calldata`, `fun_parseEvmV1`, `fun_validateBundleDestinationContext` — with
  zero sorried templates left in `specs/L2InteropHandler/`.  The L2AssetRouter generated tree
  is likewise fully built, unblocking its 312 templates as the next corpus.
  *Interpretation caveat: lossless A-specs carry exactly the concrete content; where a spec
  bottoms out at a True-AFor inner loop or the #38 call boundary, the semantic content lives
  in the corresponding concrete closed forms (#31, #50-#55, #57).*
- **#59 THE FULL ATOMIC-INTEROP ABSTRACTION LAYER (2026-07-23, second wave).**  #58's method
  extended to every corpus of the feature: **L2AssetRouter** 300/312 templates lossless (incl.
  `fun_isValidInteropSender`, `fun_recoverAtomicCall_inner`, `fun_burn`, `fun_setAssetHandler`;
  14 function pipelines built + axiom-clean), **L2InteropCommitmentTree** 33/33 (all 9 function
  pipelines axiom-clean: `fun_updateLeaf`×3, `fun_pushNewLeaf`, `fun_publishRoot`, `fun_root`,
  `fun_hashLeaf`, `fun_efficientHash`, `fun_uncheckedInc`), **AtomicFlowManager** 164/174
  (incl. `fun_checkSettlementLayerIsL1`, `fun_readAggregationHopPath`,
  `fun_verifyLastBatchInRoot`).  L1AssetRouter, L1Nullifier, DiamondProxy were already clean.
  Every unfilled residue is a dependent of a VC-GENERATOR bug, now catalogued: the known
  `EVMCleanup_bool'` cluster (AtomicFlowManager, gates `fun_verifyInclusion`/
  `fun_verifyTimeoutAbsence`), plus three new classes found in L2AssetRouter — a `log4`
  emission proof gap, two quotation parse failures (`unexpected ':'`), and an unbound-`hs`
  generated proof.  *The old pre-relocation InteropHandler corpus (316 templates) is
  deliberately skipped as superseded.*
- **#60 CROSS-CHAIN ATOMICITY, abstract core (2026-07-23).**  `IMTAbstract.lean`:
  `delivered_leg_available_forever` — delivery evidence for a leg (membership in an on-time
  settled snapshot) yields membership at EVERY later snapshot (any sibling chain verifying
  against any later published root accepts the same leg) AND the impossibility of any reclaim
  witness for it, ever.  This is the properly-named atomicity statement — executed on one
  chain ⇒ the evidence sibling chains need is permanent and unraceable — composing
  `evolution_keys_mono` with `delivered_and_reclaimed_impossible` (#34).  Per-chain
  acceptance is #57's verified ⇒ executable hook; per-chain re-execution is blocked by #50.
  *Caveat: abstract layer — the shared history `S` models the published interop roots; the
  concrete root-publication transport between chains is upstream infrastructure.*
- **#61 IMT FIDELITY, the storage-side insert agreement (2026-07-23).**
  `imt_fidelity_user.lean` (L2ICT): the abstraction function from concrete storage to the
  abstract model — `leafSlot` (`keccak(i ‖ 4)` — the `leaves` mapping base; base 5 is `valueToIndex`), `decodeLeaf` (the `value`/`nextValue` fields
  at `slot`/`+2`; `nextIndex` has no abstract counterpart), `leafSetOf` (imaged over the count
  at slot 1) — with its `sstore` frames on the CACHED branch (`sstore` grows `used_range`,
  which steers `keccak256`'s fresh-branch choice, so keccak values are `sstore`-stable only
  when cached; the accessor caches on first use).  `decodeLeaf_after_write` (a fresh struct
  write decodes exactly), `leafSetOf_after_write` (write + count bump = abstract
  `insert ⟨v, nextValue⟩`, disjointness as oracles), the keccak-injectivity discharge layer
  (`leafSlot_inj`, offset/low-slot separations over the trusted-base `keccak256_*` axioms),
  and **`leafSetOf_insert`** — the clean form: account present + count no-wrap + cached
  hashes ⇒ the storage write sequence IS the abstract set insert.  This is the first
  concrete-to-abstract link of the fidelity track that makes #60's cross-chain atomicity
  apply toward deployed code.  *Remaining: node-array no-touch frames
  (`padWalk`/`updateWalk`), composition with `pushNewLeaf_call` (P5), and the window-retarget
  half (`fun_updateLeaf`) at the AtomicFlowManager call sequence level.*
- **#62 THE STORAGE-SIDE `imtInsert` — the fidelity headline (2026-07-23).**
  `leafSetOf_imtInsert`: the AFM insert glue's leaves-mapping write sequence — retarget the
  window leaf's `nextValue` to `v`, write the new struct `⟨v, ·, W₀.nextKey⟩` at the count,
  bump the count — produces EXACTLY the abstract insert:
  `leafSetOf (…) = imtInsert (leafSetOf σ) (decodeLeaf σ widx) v`.  Hypotheses: account
  present, window index in range, count no-wrap, cached mapping hashes, and decode
  injectivity below the count (the concrete shadow of `KeyInj`).  Composed from the retarget
  agreement + the clean insert agreement + the image-update lemma +
  `Finset.Insert.comm`; every slot separation, field survival, and cache transport
  discharged internally over the trusted keccak base.  With #60
  (`delivered_leg_available_forever`) this grounds the cross-chain atomicity story in the
  deployed storage layout: the concrete insert IS an `Evolution` step's set effect.
  `leafSetOf_evolution_step` packages it with the glue's own window
  guards into the literal insert disjunct of `IMTAbstract.Evolution` — the exact step shape
  consumed by `evolution_invariant`, #34 and #60.  *Remaining: the hash-tree side
  (`pushNewLeaf_call` composition — node arrays disjoint from the leaves mapping by the
  slice-5 separations) and the glue-sequence quotation (source-verbatim (B) boundary).*
- **#63 THE INSERT GATES (L2ICT dispatcher glue, source-verbatim, 2026-07-23).**
  `imt_insert_gate_user.lean`: **the appender gate** — `insert_appender_pass/reverts`: only
  the 160-bit-masked AtomicFlowManager built-in (`0x10014`) may grow the commitment tree,
  anyone else reverts `CommitmentTreeNotAppender` (the concrete trust anchor under every
  `Evolution` step of #62); **the dedup gate** — `insert_dedup_pass/reverts`: a value already
  in `valueToIndex` reverts `IMTValueAlreadyExists` — the concrete exactly-once enforcement
  (abstract mirror `evolution_insert_unique` #46; the same gate powers the strictness upgrade
  `window_strict_of_not_mem`).  Technique debut: the glue is UNSPLIT Yul, so conditions carry
  calls — driven via `Call'`/`evalCall` with call-level closed forms (`constant_afm_call`,
  `mapping_vti_call`, `abi_encode_uint256_call`) and the call-closing recipe
  (`🧟 ∘ overwrite? ∘ setStore` + ret lookup).  The dedup pass correctly carries the
  accessor's `accOut`-threaded state.  All axiom-clean.
- **#64 REFUND MACHINE CORRECTED + STRENGTHENED for the two-step contract (2026-07-23).**
  A fresh-compile audit (stale oleans had masked it) found `no_double_refund_user` modeling a
  ONE-step refund marking `Reverted(3)`; the current contract (AtomicFlowManager.sol:134-176)
  splits it: `authorizeRefund` marks `Committed→Revertable(2)` under a missing-leg absence
  proof, `claimRefund` requires EXACTLY `Revertable` (else `ManagerLegNotRevertable`) then
  marks `Reverted(3)` and pays.  Restated and re-proven: the authorize-side and claim-side
  mark closed forms (`|||2` / `|||3`), the claim guard both ways, NEW forward liveness
  (`claim_after_authorize_passes` — the authorized leg is claimable), and the corrected
  no-double composite (`reclaim_after_refund_reverts`: after a claim the re-read is `3 ≠ 2`,
  so a second claim REVERTS — no-double-refund is the 2→3 transition).  Downstream
  `no_theft_refund` claims unchanged.  Selector recomputed independently
  (`0x83562707 = 2203461383`).  *Two regeneration renames absorbed; earlier ledger prose
  describing a single mark-3 refund should be read through this entry.*
- **#65 THE INSERT CLOSED FORM — the full glue join (2026-07-23).**
  `imt_insert_gate_user.lean`, `insertGlue_prefix`: the L2ICT `insert` dispatcher arm drives
  deterministically through all fourteen statements — appender gate, count read, the four
  guards, low-leaf read, value-order gate, the zero-iteration search, the retarget staging,
  the `updateLeaf_5205` hash interleave, the new-leaf + `valueToIndex` writes, and the
  `pushNewLeaf` interleave — under the oracle packs, ending in a 13-insert store tower and
  the composed storage/tree state (`pushOutW ∘ insertNewEvm ∘ insertUpdEvm ∘ guardsEvm`).
  Two-stage composition (`insertGlue_guards` + `insertGlue_writes`) in the
  `executeCalls_step_prefix` style; every callee at both call positions; reducible stage
  abbreviations keep the P5/5205 packs statable.  With #61-#63 and the decode agreements,
  this is the concrete half of the insert-fidelity story; the grand composition onto
  `leafSetOf_evolution_step` (#62) is the remaining stitch.
- **#66 THE GRAND FIDELITY COMPOSITION (2026-07-23).**  `glueSeq_leafSetOf`
  (`imt_fidelity_user.lean`): the insert glue's COMPLETE write sequence — retarget staging +
  copy, Merkle walk, new-leaf staging + copy, valueToIndex registration, count bump, frontier
  pad, level-0 write, root walk — produces exactly
  `leafSetOf (final) = imtInsert (leafSetOf σ₀) (decodeLeaf σ₀ widx) v` over the entry
  anchor.  The two allocator bumps split the chain into three junk-window regimes; the
  TRI-ANCHOR CACHE PACK (per index, one word cached at all three anchor intervals — the
  concrete shadow of keccak's preimage-functionality, which the model's junk-window artifact
  otherwise loses) pins every leaf slot across the whole chain, collapsing all decode
  comparisons to sload frames.  Per-index: the window leaf retargets to `⟨k_w, v⟩`, the new
  index decodes to `⟨v, W₀.nextKey⟩`, every other index is untouched, the count increments
  once.  Axiom base: the trusted keccak idealizations only.  With #65 (the concrete closed
  form whose final state instantiates this chain) and #62's capstone packaging
  (`leafSetOf_evolution_step`), the deployed insert IS an abstract `Evolution` step — and
  through #60, the cross-chain atomicity story now rests on the running bytecode.
- **#67 THE WELD (2026-07-23).**  `insertGlue_leafSetOf` (`imt_weld_user.lean`, new file) +
  `glueSeq_leafSetOf'` (`imt_fidelity_user.lean`, interleave-accurate variant of #66; the
  original kept intact): #66's generic chain instantiated with #65's VERBATIM dispatcher
  final state `wFinal` — `leafSetOf (wFinal …) = imtInsert (leafSetOf evm) (decodeLeaf evm
  IX) V`, anchored at the dispatcher ENTRY state (the guards bridge is proven inside).
  Both commissioned deviations absorbed: the update interleave's hashLeaf step + level-0
  write (generic-H1 segment, 32-vs-64 preimage split), and the read-backs DISCHARGED as
  theorems (`guards_slot_pins`: the pack word at IX is the guards' computed slot, by
  entry-interval cache functionality) rather than hypothesized.  One NEW deviation found
  and absorbed: the push interleave hashes the new-leaf struct BEFORE the count bump — a
  fifth junk-window regime; the cache pack is now FIVE-ANCHOR (entry / guardsEvm / E4 /
  F4 / H3).  Support: `sload_hashLeafOut_of_clean`, `leafRead_mload_key/nextKey`,
  `guards_sload`.  Axiom base: trusted keccak only.  The deployed insert's set effect is
  now ONE theorem from the entry state; remaining to Evolution packaging: the window
  discharge (#68).
- **#68 THE EVOLUTION PACKAGING (2026-07-23).**  `insertGlue_evolution` /
  `insertGlue_evolution_step` / `evolution_disjunct_of_step` (`imt_weld_user.lean`): the
  real dispatcher pass IS the abstract `Evolution` insert disjunct.  The window is DERIVED
  from the contract's own guards (Yul ground truth: lower check STRICT, upper check WEAK
  with `nextValue = 0` last-leaf sentinel, dedup requires `valueToIndex[V] = 0`), through
  the read-back discharge + entry-anchor transport; membership from the count bound;
  strictness via `window_strict_of_not_mem`; the set equation from #67.  Residue, named
  and documented: `NextClosed` (free along any history from sound genesis via
  `evolution_sound`) and `hfresh : V ∉ keys` — whose concrete pin `valueToIndex[V] = 0`
  awaits the vti-coherence invariant (#69), the single genuinely new obligation left.
  Axiom base: trusted keccak only.
- **#69 VTI-COHERENCE — THE ARC CLOSES (2026-07-23).**  `imt_vti_user.lean` (new):
  `VtiCoherent` (every nonzero decoded key has a nonzero `valueToIndex` entry; the key-0
  carve-out is forced by genesis, which seeds `leaves[0]=⟨0,0,0⟩` without a vti entry) with
  the bridge `hfresh_of_dedup_gate` — the dedup gate's `valueToIndex[V]=0` pin IS abstract
  key-freshness (definitional at the entry state) — and full preservation through the
  deployed insert (`Sep32` walk-frame family: every 32-byte-preimage array slot misses every
  64-byte-preimage leaf/vti slot; the key set gains exactly V by #67's equation; V's new
  entry is the count, nonzero by the contract's own initialized guard).  CAPSTONE
  `insertGlue_evolution_closed`: #68's step theorem with freshness REPLACED by the invariant,
  and the invariant re-established at the post-state — invariant in, invariant out.  The
  leaf-set arc is now closed end-to-end: every hypothesis is either a contract guard pin,
  a documented junk-window cache pack (model artifact), or `NextClosed` (free along any
  history from sound genesis).  Axiom base: trusted keccak only.

## Part B addendum — 2026-08-11: cross-key storage isolation

Every result in Part B about a status, state or flag is about ONE mapping entry: the bundle whose
status is written, the leg whose refund state is set, the withdrawal whose flag is finalized.  None
of them says anything about a DIFFERENT entry.  That leaves a family of attacks unaddressed — not
forging a value at its own slot, but reaching it sideways from another key.

This addendum records the results closing that, all axiom-free (they use the DERIVED keccak facts of
the Part D trusted-base note, not the idealizations).

| what | where | depth |
|---|---|---|
| bundle delivery status | `AttackVectors/NoCrossBundle.lean` | 1 (`bundleStatus[bh]`) |
| leg refund state | `AttackVectors/NoCrossLeg.lean` | 2 (`_state[flowId][bundleHash]`) |
| withdrawal finalized flag | `AttackVectors/NestedSlots.lean` | 3 (`[chainId][batch][index]`) |
| any depth | `NestedSlots.nestedSlot_inj` | n |

Each family covers both the CACHED case (keys the run has already hashed — via cache injectivity)
and the UNSEEN case (a key whose slot has never been computed — via freshness, a different argument
with the same conclusion), and both single writes and whole SEQUENCES of them, which is the form a
refund or delivery loop needs.

**Three of these compose into rejection statements, not just state facts:**

* `NoCrossLeg.flow_substituted_claim_reverts` — an authorization for `(flowId₁, bundleHash)` cannot
  be ridden by a claim for `(flowId₂, bundleHash)`.  This is the mirror of A6′'s
  `crafted_claim_reverts_after_authorization`, which requires the BUNDLE HASHES to differ and so
  leaves the flow coordinate open.  A bundle hash commits to contents, not to a flow.
* `NoReplayCross.replay_still_reverts_after_other_finalization` — a finalized withdrawal's replay
  guard still fires after an attacker finalizes whatever else they can reach.
  `replay_after_set_reverts` shows no replay with nothing else touching storage; this shows the
  protection is not aliasable.
* `InteropHandler.Layout.unverified_stays_unverified` — marking one bundle cannot make another pass
  the verified gate.

**And one does not**, which is the honest asymmetry: bundle DELIVERY has only the state half, because
its guard is not extracted.  See the Part D addendum of the same date.

## Part C — What a reviewer should do

1. **Read Part A** and decide if the assumptions are acceptable for your threat model (especially
   A1 solc trust, A3 admitted MCOPY/TSTORE, A4 revert model, A8 scope).
2. **Cross-check the storage slot numbers (A7)** against the Solidity storage layout.
3. **For each statement in Part B,** decide whether the plain-English claim is the property you want,
   and whether the caveat is acceptable.
4. The proofs themselves need no review — re-running `lake build` re-verifies them with the kernel.

## Part D — What is NOT yet covered (honest gaps)
- **"Only Bridgehub/NTV/Nullifier can move funds"** (caller authorization) — **substantially addressed** by
  #15 (BRIDGE_HUB) and #16 (NativeTokenVault, the actual fund-mover-into-NTV path, with the authorized address
  pinned to a real storage read). For both, the operands + guard literal are pinned; the actual comparison +
  revert-routing remain uncovered (inlined in the dispatch switch, too heavy to compile post-regeneration). The
  analogous **L1_NULLIFIER** guard (`msg.sender == L1_NULLIFIER`, immutable 92, Yul line 604, selector
  `0x9c884fd1`) is present in the Yul but **the VC generator does not emit it** — `loadimmutable("92")` and that
  selector appear nowhere in the generated Lean (a codegen coverage gap; BRIDGE_HUB's `loadimmutable(75)` *is*
  emitted). It cannot be proven without extending the generator. Withdrawal anti-drain is in any case covered by #1.
- **"No withdrawal without a verified Merkle proof"** (proof-required-for-withdrawal) — **DONE as #20**
  (the whnf wall was removed by the block-chunking regeneration). Verified modulo A3 (see #20's caveat).
- **DiamondProxy facet routing** — the *slot computation* (#13) and *facet-record decode* (#14) are
  now proven (the whnf wall on the struct-storage read was removed by the block-chunking generator
  fix). What remains uncovered is only the **final `delegatecall` dispatch step** itself — that the
  proxy actually delegates to the decoded facet address (and the `isFreezable`/frozen-state guard).
- The cleaner success⇒precondition form of guard theorems: **DONE for #5 (checkOwner)→#17, #6
  (requireNotPaused)→#18, and #4 (validateChainParams gates 1–8)→#19** via the new `reverted` flag. Remaining:
  validateChainParams gate 9 (double-`iszero`, keccak-fanout timeout — not extracted); and #15/#16 (BRIDGE_HUB/NTV)
  which can't use this directly (their `eq`+revert is inlined in the un-buildable dispatch switch, not a
  standalone guard function).
- Liveness, cross-contract end-to-end, L2/prover — out of model scope (A8).

### Part D addendum — 2026-08-11: no-double-DELIVERY is proved at the state level, not the guard level

`delivered_status_reads_two` (`no_double_delivery_user.lean`) proves that after `_markFullyExecutedAndRun`'s
write, the bundle's status slot reads `2 = FullyExecuted`.  Its security reading — "a second delivery of
the same bundle is REJECTED by its own first write" — needs one more step: that the execute/receive path
ACCEPTS ONLY `Unreceived`/`Verified`, so a `2` is refused.

**That step is prose, not a theorem.**  The file header asserts it ("the execute/receive paths accept only
`Unreceived`/`Verified`, read in `fun_getBundleData`"), and `fun_getBundleData_user.lean` — the spec of the
function that performs the read — is a `sorry` stub (`A_fun_getBundleData := sorry`).  Grep for revert
theorems in `specs/InteropHandler/` returns only `unauthorized_sender_reverts` and `not_included_reverts`,
both of which gate the VERIFY path; `exec_allowed_user.lean`'s `auth_self_pass` / `auth_executor_pass` gate
the CALLER, not the bundle's status.  So no theorem anywhere says a `FullyExecuted` bundle is refused.

What IS proved on this path, and it is not nothing: the status byte reads `2` after the mark
(`delivered_status_reads_two`), and no other bundle's byte can be moved to fake or clear that value
(`InteropHandler.Layout.statusOf_frames_other_bundle` / `unverified_stays_unverified`, and
`AttackVectors.NoCrossBundle` for the cached and unseen cases).

**Contrast with the refund path, which IS complete.**  There the guard is extracted
(`refund_check_reverts`), so the theft statements compose end to end: `crafted_claim_reverts_after_authorization`
for a substituted bundle hash, and `AttackVectors.NoCrossLeg.flow_substituted_claim_reverts` for a substituted
flow.  Both conclude `reverted = true` — an actual rejection, not just a state fact.  Delivery has the state
half of that shape and is missing the guard half.

Closing it needs the execute-path status check extracted as a block-level theorem, which is a VC-generation
and block-spec task rather than a reasoning one.

### Part D addendum — atomic-interop gaps as of 2026-07-23 evening

- ~~**The grand fidelity stitch**~~ — **CLOSED** by #67, `insertGlue_leafSetOf`
  (`imt_weld_user.lean`): `leafSetOf (concrete final evm) = imtInsert (leafSetOf evm)
  (decodeLeaf evm IX) V`, i.e. exactly the single theorem this bullet said was missing.
  `sorry`-free; depends on all four keccak idealizations.  *(Bullet corrected 2026-08-11 — it
  described the state as of 2026-07-23 and the weld post-dates it.  Both this and the
  trusted-base bullet above were found stale by the same audit; a reviewer-facing gap list that
  overstates the gaps is a smaller problem than one that understates them, but it is still wrong.)*
- **VC-generator bugs** (GENERATOR_BUGS.md): four classes gate 22 templates —
  `EVMCleanup_bool'` (gates `fun_verifyInclusion`/`fun_verifyTimeoutAbsence` pipelines;
  their CONCRETE coverage exists in #22–#36), raw revert-strings in quotations, a lone-callee
  `hs` bug, and a `log4` shape gap.  Upstream fixes make ~22 templates fill mechanically.
- **Loop abstractions carry `True`-`AFor`** everywhere except `fun_executeCalls` (free
  inductive) — per-loop effect content lives in the concrete closed forms (#31, #55, #65),
  not the abstraction pipelines.
- **Trusted base**: A3/A2a/A8 model caveats, and the junk-window discipline (cached-branch
  hypotheses throughout the storage layer).  All uses traceable via `#print axioms`.

  **UPDATED 2026-08-06 — the four keccak idealizations now all have DERIVED counterparts.**
  In Clear's model a keccak result is not a hash: it is drawn from `keccak_range`, the pool of
  fresh slots.  So these are properties of the POOL, provable from how it is configured, and the
  invariants survive because the set of slots a state can produce only ever shrinks.

  | idealization | derived counterpart | reduces to |
  |---|---|---|
  | `keccak256_inj` | `KeccakSeqInj.keccakOut_seq_ne` | single-thread reasoning |
  | `keccak256_ne_lowSlot` | `KeccakLowSlot.keccak256_ne_lowSlot_of_config` | pool has no low slot |
  | `keccak256_slot_sep` | `KeccakSlotSep.keccak256_slot_sep_of_config`, `cached_off_ne_off` | pool pairwise separated |
  | `keccak256_add_ne_lowSlot` | `KeccakLowSlot.keccak256_add_ne_lowSlot_of_config` | two-sided pool window |

  This RELOCATES the assumption rather than removing it: a reader must still grant the pool
  configuration.  Two things stay genuinely irreducible, and deriving the rest is what made them
  visible: (i) CROSS-THREAD injectivity — two independent fresh picks in disjoint state threads
  really could coincide, which is why `keccak256_inj` is stated without a global hash function in
  the first place; (ii) the derived route cannot speak about a FRESH result at all, since it is not
  in the cache, so `cached_off_ne_off` takes cache HITS where the axiom takes bare successful calls.

  Axiom-free variants exist for all three frame routes (`leafSetOf_{arr,vti,lowSlot}Write_of_config`).
  The ORIGINALS are deliberately left in place and are still the ledger's non-clean entries — these are
  parallel routes, not replacements, so no existing caller changed.  Switching the no-theft chain over
  is a decision about the corpus's trusted base, not a proof task.

  Coverage of the ledger itself is checkable: `./scripts/axiom-sweep.sh specs/AttackVectors Audit`
  enumerates theorems from source and flags any non-clean result the ledger omits (it found two
  missing entries on first run).  As of 2026-08-11: 123 clean of 127 in `specs/AttackVectors`, and
  301 of 310 across `specs/`, with every non-clean result either a frame route or inside
  `KeccakInjective.lean` itself.
- **A spec file that did not compile** (found AND repaired 2026-08-11): `imt_root_atlas_user.lean`
  had been broken for an unknown period, leaving its **72 theorems unverified**.  It compiles now.
  Nothing imported it and nothing in this document cited it, so no claim here ever rested on it.
  All five errors had two causes: one dangling reference to a deleted helper
  (`byte_mstore32_pinned`, reconstructible from its use site with no new reasoning), and three
  instances of `atlasH_at_hash_state`'s state argument being left implicit, which made the
  elaborator search for a state inside a four-deep `mstore` tower instead of proving anything.
  It was found only because `scripts/axiom-sweep.sh` could not sweep its directory — **no other
  check in the corpus notices a file that nothing imports**, which is the part worth keeping.

  That gap is now covered directly by `./scripts/unbuilt-check.sh`, which lists every spec file with
  no `.olean` (cheap — it only stats files, no Lean runs).  As of 2026-08-11: **70 of 2714**, and
  sampling them puts every one in a known class rather than a new surprise:

  | count | location | class |
  |---|---|---|
  | 36 + 7 | `L2AssetRouter` | blocked upstream — raw revert-strings in quotations (`GENERATOR_BUGS.md`) |
  | 12 | `L2InteropHandler` | same generator class |
  | 3 + 7 | `AtomicFlowManager` | blocked upstream — `EVMCleanup_bool'`, the documented gate on `fun_verifyInclusion` / `fun_verifyTimeoutAbsence` / `fun_authorizeRefund` |
  | 5 | `specs/KDParallel` | untracked scratch, not part of the corpus |

  The distinction that matters when reading that list: a spec blocked by a `generated/` bug is
  expected and recorded, whereas a HAND-WRITTEN spec that stopped compiling is silent breakage.
  Tell them apart by building the module and checking whether the first error is in `generated/` or
  in `specs/`.  `imt_root_atlas_user` was the only instance of the second kind, and it is fixed.
- **Ledger coverage, and how to read the ratio** (`specs/AttackVectors/Audit.lean`): the ledger's
  numerator is checked by Lean, but its denominator is a hand-maintained claim about which results
  are listed.  `./scripts/axiom-sweep.sh <dir> Audit` checks that denominator by enumerating theorems
  from source.

  **The ledger's ratio is NOT representative of the corpus, and should not be read as one.**  It
  samples headline results, and those skew to the abstract and attack-vector layers, which are
  naturally axiom-free.  Sweeping whole directories gives the real distribution:

  | directory | clean / total | note |
  |---|---|---|
  | `specs/AttackVectors` | 123 / 127 | the 4 non-clean are the frame routes, all in the ledger |
  | `specs` (Clear layer) | 301 / 310 | the 9 non-clean are all inside `KeccakInjective.lean` itself |
  | `specs/L2InteropCommitmentTree` | 115 / 155 | **~1 in 4 depends on the keccak idealizations** (was 65/97 before `imt_root_atlas_user` was repaired) |
  | `specs/AtomicFlowManager` | 39 / 48 | 9 non-clean, and **every one of them uses only `keccak256_inj`** |

  The third row is the honest one for the concrete storage layer: slot separation and low-slot
  avoidance are needed at nearly every step that reasons about which storage slot a write touches, so
  the intermediate lemmas (`leafSlot_inj`, `decodeLeaf_*`, `*_sload_one`, the `glueSeq`/`insertGlue`
  family) carry the axioms and so does everything built on them.  Listing every one of those in the
  ledger would be noise; the capstones are listed (`insertGlue_leafSetOf`, `insertGlue_evolution`,
  `insertGlue_evolution_step`, `leafSetOf_evolution_step`, `leafSetOf_imtInsert`,
  `root_pins_written_leaf`), and the sweep is how to see the rest.

  The `AtomicFlowManager` row's nine non-clean results depend on `keccak256_inj` ALONE, which is the
  one idealization with a single-thread derived counterpart (`KeccakSeqInj.keccakOut_seq_ne`).  That
  looked like a migration opportunity.  **It is not — checked 2026-08-11, and the check settles it:
  every one of the nine quantifies over TWO INDEPENDENT STATES.**

      accOut_inj, commitValueOut_inj, hashLeafOut_inj,
      accessor_slots_differ_of_key_ne, crafted_claim_reverts_after_authorization   {σ₁ σ₂ : EVMState}
      same_position_member_gap_impossible                       {σ₁ σ₂} + {σf₁ σf₂}
      flowid_pins_legcount                                      {σ₁ σ₂ σ₁' σ₂'}
      foldRoot_binding                                          {σ₁ σ₂}
      flowid_pins_deadline_sl                                   {E₁ E₂ σ₁' σ₂'}

  Two unrelated states is exactly the case the derived route cannot reach and `keccak256_inj` exists
  for — `KeccakInjective`'s own header says it is stated without positing a global hash function
  because independent fresh picks in disjoint threads could coincide.  These theorems USE that
  generality deliberately: a binding claim about two separately-computed slots is stronger, and more
  useful to a reviewer, than one restricted to a single execution.

  So the axiom is load-bearing here for a principled reason, and migrating these would WEAKEN them
  rather than clean them up.

  **The `L2InteropCommitmentTree` layer is the opposite case, and that is the actionable finding.**
  Triaging its 32 non-clean results the same way: 13 of the 14 core ones are stated over a SINGLE
  state, and the one exception (`leafBase_sep`, `{σ₁ σ₂ σ₁' σ₂'}`) has no callers anywhere in the
  corpus — it is standalone.  The insert chain itself is single-thread throughout: `glueSeq_leafSetOf'`
  binds three states (`evm`, `H1`, `H3`), but those are the entry state and the two `hashLeaf` bumps
  of ONE execution, not independent runs.

  So the derived route applies in principle all the way up to `insertGlue_leafSetOf` — the grand
  fidelity stitch could be made axiom-free.  The work is bounded but not small: roughly thirty
  intermediate lemmas each need an `_of_config` variant threading the pool hypotheses
  (`RangeInWindow` / `CachedInWindow` / `Separated` / `CacheInj`), in the state-matching style of
  `leafSetOf_{arr,vti,lowSlot}Write_of_config`, and then the chain rethreaded.  Nobody should start
  that without deciding it is wanted: it trades an appeal to keccak's output distribution for a
  configuration hypothesis on the fresh-slot pool, and both routes are defensible.

  **A caveat on the triage method**, since it is easy to misuse: counting state binders is a
  HEURISTIC, not the criterion.  What matters is whether the states are RELATED BY EXECUTION.  The
  `AtomicFlowManager` results take two `keccak256 … = some` hypotheses with no relation between
  `σ₁` and `σ₂` — genuinely disjoint threads.  `glueSeq_leafSetOf'` takes three binders that are
  stages of one run.  Binder count alone would have classified the second as harder than the first,
  which is backwards.  The honest summary of the whole derivation effort: it removes the
  idealization where the corpus reasons within one execution (the frame routes, the forgery track),
  and leaves it exactly where the corpus deliberately reasons across executions.

  Note also `specs/*/…/Common/` (the per-block specs, ~1700 files) is deliberately NOT swept: those
  are overwhelmingly `A := concrete` aliases, so they would report clean while proving nothing and
  would swamp the ratio.  Measuring them needs the `#print axioms`-vs-alias distinction, not this tool.

  Two modules had never been built at all when the sweep first ran: `mcopy.lean` (fine — it compiles,
  nobody had compiled it) and `imt_root_atlas_user.lean` (broken, see above).
- **Verification hygiene** (added after today's audits): `lake env lean` does not check
  import-olean freshness — corpus-level claims require fresh-compile audits; two silent
  regressions (renamed helpers, a renumbered enum) were found and repaired this way (#64,
  b696185).  The old pre-relocation InteropHandler corpus is deliberately unmaintained.
