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
  `committed_member_gap_impossible`).
- **The tree-builder is verified against a pure model** — `fun_updateLeaf` end-to-end equals the
  pure walk `updateWalk` (leaf write + per-level sibling hash + parent store) (*#31* + U4), and
  **the gates' verifier fold replays that walk** — given the walk's cache, siblings, and scratch
  window, `foldRoot` recomputes exactly the stored root (*#32*, axiom-free), and **the stored root
  admits ONLY the written leaf** — any collision-free fold reaching it at that position carries
  the builder's leaf (`root_pins_written_leaf`, *#32* + *#27*, A6′). Remaining for the full
  capstone discharge: the dispatcher-inlined insert glue → `imtInsert` correspondence
  (source-level inspection; outside the generated corpus).

33 machine-checked theorem groups in total (Part B), on top of a 485/485 real-build baseline (A9). The
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
