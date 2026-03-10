# Cross-Chain Balance Preservation Roadmap

## Goal

Prove a theorem for the L1 asset-router deposit path stating that, on successful execution,
the amount removed from L1 custody is exactly the amount represented in the outbound
cross-chain message, so total value is preserved as:

- L1 custody after the call
- plus in-flight bridge message amount
- equals
- L1 custody before the call

This is the concrete target behind the informal statement:

> cross-chain bridging preserves funds across chain + in-flight funds

## Current Distance To Goal

We are not close to the final theorem yet, but the path is now clear.

Roughly:

- wiring and module hygiene: mostly done
- small helper infrastructure: partly done
- exact encoding lemmas: partly done
- custody-side amount lemma: not done
- top-level composition theorem: not done

Pragmatic estimate:

- about 20% complete for the final invariant
- about 60% complete for unblocking the proof pipeline structurally

The main reason the final theorem is still far away is that the key semantic bridge is
missing in the middle:

- a lemma that the custody transfer path actually moves exactly `var_amount`
- a lemma that the outbound calldata encodes exactly that same amount
- a composition theorem that links those two facts inside the deposit function

## What Is Already In Place

### Structural progress

- `generated.L1AssetRouter_clean` namespace drift appears cleaned up.
- `finalize_allocation_user` now builds as an identity abstraction.
- a local `mcopy` shim now builds.
- the helper control-flow file `if_7322987041177811756_user` builds.

### Finished or mostly-finished useful proofs

- `specs/L1AssetRouter/L1AssetRouter/abi_encode_uint256_address_address_user.lean`
  proves the exact memory effect of the three-word ABI encoder.
- `specs/DiamondProxy/DiamondProxy/cleanup_bool_user.lean`
  is a separate complete proof and serves as a style reference.

### Important semantic footholds already visible in generated code

- `generated/L1AssetRouter/L1AssetRouter/fun_transferFundsToNTV_inner_gen.lean`
  contains the local amount-consistency check:
  - `let diff := 0` / later update of `diff`
  - `if iszero(eq(diff, var_amount)) { revert(0, 0) }`
- `generated/L1AssetRouter/L1AssetRouter/fun_bridgehubDepositNonBaseTokenAsset_gen.lean`
  already composes:
  - `fun_encodeBridgeBurnData`
  - `fun_getDepositCalldata`

This means the right proof shape is available; it is just not abstracted yet.

## Current Blockers By Layer

### Layer 1: helper plumbing

These are mostly in acceptable shape, but some helper specs still use `sorry` and will
eventually need tightening:

- `specs/L1AssetRouter/L1AssetRouter/array_allocation_size_bytes_user.lean`
- `specs/L1AssetRouter/L1AssetRouter/abi_encode_bytes_user.lean`
- `specs/L1AssetRouter/L1AssetRouter/abi_decode_bytes_fromMemory_user.lean`

These are not the final theorem, but they sit directly on the deposit-calldata path.

### Layer 2: encoding lemmas

These are the next serious blockers:

- `specs/L1AssetRouter/L1AssetRouter/fun_encodeNTVAssetId_user.lean`
  - currently does not build
  - has parser issues from direct projections like `(foo ... )["bar"]!!`
- `specs/L1AssetRouter/L1AssetRouter/fun_encodeBridgeBurnData_user.lean`
  - currently fails with a type mismatch
  - the current proof ends with `exact hconcrete`, which is not strong enough

### Layer 3: custody lemma

This is the most important missing semantic theorem:

- `specs/L1AssetRouter/L1AssetRouter/fun_transferFundsToNTV_inner_user.lean`
  - still entirely `sorry`

Without this, we do not yet know that the amount pulled into custody equals the requested
bridge amount.

### Layer 4: deposit-message construction

- `specs/L1AssetRouter/L1AssetRouter/fun_getDepositCalldata_user.lean`
  - still entirely `sorry`

This is where the encoded outbound message needs to be tied to the semantic amount field.

### Layer 5: top-level bridge theorem

- `specs/L1AssetRouter/L1AssetRouter/fun_bridgehubDepositNonBaseTokenAsset_user.lean`
  - still entirely `sorry`

This is the final composition point for the L1-side theorem.

## Recommended Target Theorem Stack

The proof should be built bottom-up as a stack of lemmas. Do not jump directly to the
top-level invariant.

### Milestone A: exact low-level data lemmas

Goal:

- prove exact semantics for memory allocators and ABI byte encoders/decoders used by the
  deposit path

Required outputs:

- exact or at least compositional specs for:
  - `array_allocation_size_bytes`
  - `abi_encode_bytes`
  - `abi_decode_bytes_fromMemory`
  - `fun_encodeNTVAssetId`
  - `fun_encodeBridgeBurnData`

Acceptance criteria:

- each target builds through its generated bridge file
- no syntax errors
- no raw identity spec unless the function is truly a pure control-flow helper

### Milestone B: custody-side amount preservation lemma

Goal:

- prove that `fun_transferFundsToNTV_inner` implies:
  - success means no revert on the `diff` check
  - observed transferred amount equals `var_amount`

Suggested abstract statement:

- on successful return, there exists an internal observation `diff` such that:
  - `diff = var_amount`
  - the output state records the custody-side transfer result used by callers

Minimum acceptable version:

- a successful call implies the path passed the `iszero(eq(diff, var_amount))` guard
- therefore the effective transferred amount equals `var_amount`

Acceptance criteria:

- `generated.L1AssetRouter.L1AssetRouter.fun_transferFundsToNTV_inner` builds
- the theorem exposes an amount equality that callers can reuse

### Milestone C: message-side amount preservation lemma

Goal:

- prove that `fun_getDepositCalldata` constructs a deposit message whose encoded amount
  field equals the semantic deposit amount

This likely depends on:

- `fun_encodeBridgeBurnData`
- `abi_encode_bytes`
- `abi_decode_bytes_fromMemory`
- allocation helpers

Acceptance criteria:

- `generated.L1AssetRouter.L1AssetRouter.fun_getDepositCalldata` builds
- the resulting abstraction states exactly where the bridged amount is stored or encoded

### Milestone D: top-level deposit composition

Goal:

- prove that `fun_bridgehubDepositNonBaseTokenAsset` composes:
  - custody transfer
  - asset-id encoding
  - bridge-burn data encoding
  - deposit calldata construction

Suggested abstract statement:

- if the function returns successfully, then:
  - the amount removed from custody is `A`
  - the outbound deposit calldata encodes amount `A`
  - therefore total value is preserved across custody plus in-flight message state

Acceptance criteria:

- `generated.L1AssetRouter.L1AssetRouter.fun_bridgehubDepositNonBaseTokenAsset` builds
- theorem contains an explicit shared amount variable linking custody and message encoding

### Milestone E: final system-level invariant wrapper

Goal:

- state the user-facing theorem in invariant language rather than function-local language

Example shape:

- define a function-level invariant predicate:
  - `BalancePreservedAcrossCustodyAndMessage ...`
- prove it from `A_fun_bridgehubDepositNonBaseTokenAsset`

This layer should mostly be clean theorem packaging, not new symbolic execution.

## Detailed Work Plan

### Track 1: encoding repair

Files:

- `specs/L1AssetRouter/L1AssetRouter/fun_encodeNTVAssetId_user.lean`
- `specs/L1AssetRouter/L1AssetRouter/fun_encodeBridgeBurnData_user.lean`

Work:

1. Refactor `fun_encodeNTVAssetId_user` to avoid parser-hostile projected expressions.
2. Name intermediate states explicitly:
   - `let s_call := ...`
   - `let s_preFinalize := ...`
   - `let s_preKeccak := ...`
3. Use the existing `A_abi_encode_uint256_address_address` lemma compositionally.
4. Finish the concrete-to-abstract proof with `spec_eq`, `clr_funargs`, and `simpa`.
5. Do the same for `fun_encodeBridgeBurnData_user`, but include the finalize-allocation step.

Why this matters:

- these lemmas produce the exact in-flight payload that later the top-level theorem must
  compare against custody movement

### Track 2: helper strengthening

Files:

- `specs/L1AssetRouter/L1AssetRouter/array_allocation_size_bytes_user.lean`
- `specs/L1AssetRouter/L1AssetRouter/abi_encode_bytes_user.lean`
- `specs/L1AssetRouter/L1AssetRouter/abi_decode_bytes_fromMemory_user.lean`

Work:

1. Replace broad `sorry` placeholders with compositional postconditions.
2. Keep specs minimal but semantically useful.
3. Avoid spending time over-specifying irrelevant memory details if the parent theorem only
   needs length or copied-bytes facts.

Why this matters:

- `fun_getDepositCalldata` will be much easier to prove if these helpers already expose the
  right byte-array semantics

### Track 3: custody invariant extraction

File:

- `specs/L1AssetRouter/L1AssetRouter/fun_transferFundsToNTV_inner_user.lean`

Work:

1. Inspect the generated path around the `diff` computation and equality guard.
2. Write an abstraction centered on amount preservation, not full state equality.
3. Capture only the facts needed by callers:
   - successful call
   - custody transfer observed
   - observed amount equals `var_amount`

Why this matters:

- this is the custody half of the final theorem

### Track 4: deposit calldata semantic extraction

File:

- `specs/L1AssetRouter/L1AssetRouter/fun_getDepositCalldata_user.lean`

Work:

1. Identify which switch arm corresponds to the successful non-base-token deposit path.
2. State a spec that exposes:
   - constructed calldata pointer
   - encoded deposit amount
   - dependency on caller/asset/message data
3. Avoid proving everything about calldata layout if only the amount field is needed.

Why this matters:

- this is the message half of the final theorem

### Track 5: top-level composition

File:

- `specs/L1AssetRouter/L1AssetRouter/fun_bridgehubDepositNonBaseTokenAsset_user.lean`

Work:

1. Abstract over the successful path only.
2. Reuse:
   - custody lemma from `fun_transferFundsToNTV_inner`
   - message lemma from `fun_getDepositCalldata`
   - encoding lemma from `fun_encodeBridgeBurnData`
3. Introduce one shared semantic amount symbol and prove both sides equal it.
4. Build this proof bottom-up.
   - First make the helper `_user` files build on their own.
   - Then prove the small encoding/control-flow/custody lemmas as leaf targets.
   - Only after those are stable, assemble the bridge-level composition theorem.
   - Do not mock or shortcut the large bridge proof by starting from the top-level statement and patching dependencies downward.

Why this matters:

- this is the first place the final invariant actually becomes visible
- the proof development order should follow the dependency order, even though this workflow note is not itself on the manual-review path

## Manual Review List

This section lists only the major statements that should be reviewed by a human.
Helper lemmas, parser repairs, allocation lemmas, and control-flow plumbing should not be
on the manual-review critical path unless they change one of these statements.

### What should be reviewed

1. `A_fun_transferFundsToNTV_inner`
   in `specs/L1AssetRouter/L1AssetRouter/fun_transferFundsToNTV_inner_user.lean`
   - This is the custody-side statement.
   - It is where we assert that successful bridging locks exactly the requested amount.
   - Review question:
     - does this really capture "locked balances are preserved" for the actual NTV custody path?

2. `A_fun_getDepositCalldata`
   in `specs/L1AssetRouter/L1AssetRouter/fun_getDepositCalldata_user.lean`
   - This is the outbound message statement.
   - It should say that the in-flight cross-chain calldata represents the same amount.
   - Review question:
     - does this actually mention the amount encoded into the message, rather than just pointer plumbing?

3. `A_fun_bridgehubDepositNonBaseTokenAsset`
   in `specs/L1AssetRouter/L1AssetRouter/fun_bridgehubDepositNonBaseTokenAsset_user.lean`
   - This is the real contract-entrypoint statement for the L1 non-base-token bridge path.
   - This is the most important spec to review.
   - Review questions:
     - is this the right contract function?
     - is it the right bridge path?
     - does it explicitly connect custody movement and outbound message contents?

4. `BridgedAmountPreserved`
   in `specs/L1AssetRouter/L1AssetRouter/bridged_amount_preserved_user.lean`
   - This is the invariant-shaped statement.
   - It is the clearest place to review the intended theorem wording:
     - balances locked in custody
     - plus balances represented in-flight
     - preserve total value
   - Review question:
     - is this the right invariant statement, or does it still talk too much about low-level state variables like `expr_9` and `expr_6`?

5. `bridgehubDepositNonBaseTokenAsset_preserves_bridged_amount`
   in `specs/L1AssetRouter/L1AssetRouter/fun_bridgehubDepositNonBaseTokenAsset_user.lean`
   - This should be the theorem that ties the actual bridge entrypoint to the invariant.
   - Review question:
     - does this theorem really derive the invariant from the contract path, or is it only a wrapper around lower-level assumptions?

### Current important caveat

Right now, the major invariant statement exists, but it is not yet fully connected to the
actual contract proof.

Concretely:

- `BridgedAmountPreserved` exists in
  `specs/L1AssetRouter/L1AssetRouter/bridged_amount_preserved_user.lean`
- `bridgehubDepositNonBaseTokenAsset_preserves_bridged_amount` also exists in
  `specs/L1AssetRouter/L1AssetRouter/fun_bridgehubDepositNonBaseTokenAsset_user.lean`
- but `A_fun_bridgehubDepositNonBaseTokenAsset` and
  `fun_bridgehubDepositNonBaseTokenAsset_abs_of_concrete` are still `sorry`

So the current state is:

- the invariant has been stated
- the intended top-level theorem has been named
- but the proof is not yet tied end-to-end to the real bridge entrypoint

### Review rule

If you only review one thing, review this chain:

1. `A_fun_transferFundsToNTV_inner`
2. `A_fun_getDepositCalldata`
3. `A_fun_bridgehubDepositNonBaseTokenAsset`
4. `BridgedAmountPreserved`
5. `bridgehubDepositNonBaseTokenAsset_preserves_bridged_amount`

That is the full theorem-level spine. Everything else is implementation detail.

## Proof Design Rules

### What to prove exactly

Prefer proving amount equalities and specific memory facts over full-state equality.

Good abstraction:

- "the encoded amount in the message equals `var_amount`"

Bad abstraction:

- "the entire final state equals some giant concrete store expression"

### What can remain weak

It is acceptable for helper specs to stay intentionally weak if:

- they are pure control-flow wrappers
- they do not contribute semantic facts needed by parent proofs

Examples already acceptable for now:

- `finalize_allocation_user`
- `mcopy` shim

### What cannot remain weak

These must eventually expose real semantics:

- `fun_transferFundsToNTV_inner`
- `fun_getDepositCalldata`
- `fun_bridgehubDepositNonBaseTokenAsset`
- the encoding helpers that determine amount bytes

## Recommended Agent Ordering

Do not work on the final theorem first.

Recommended order:

1. fix `fun_encodeNTVAssetId_user`
2. finish `fun_encodeBridgeBurnData_user`
3. strengthen byte-array helpers
4. prove `fun_transferFundsToNTV_inner_user`
5. prove `fun_getDepositCalldata_user`
6. compose in `fun_bridgehubDepositNonBaseTokenAsset_user`
7. wrap the final invariant theorem

## Definition Of Done

We should consider the final goal reached only when all of the following are true:

- `fun_transferFundsToNTV_inner_user` proves custody-side amount equality
- `fun_getDepositCalldata_user` proves message-side amount equality
- `fun_bridgehubDepositNonBaseTokenAsset_user` composes both into one theorem
- the final theorem is stated in invariant language:
  - value before
  - equals value after in custody plus in-flight representation

## Immediate Next Actions

If resuming work right now, do this:

1. repair syntax and projections in `fun_encodeNTVAssetId_user`
2. finish `fun_encodeBridgeBurnData_user`
3. extract the `diff = var_amount` theorem from `fun_transferFundsToNTV_inner_user`

That is the shortest path to making the final theorem reachable.
