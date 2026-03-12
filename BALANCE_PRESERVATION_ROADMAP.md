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

---

## Accurate Bridge Call Chain (from era-contracts source)

This section documents the actual contract call chain derived from reading the
era-contracts Solidity source. The extension section below uses this as the basis
for the full system-level invariant.

### L1 → L2 deposit (non-base token)

The user-facing entry point is on the Bridgehub, not L1AssetRouter directly.

```
User
  → Bridgehub.requestL2TransactionTwoBridges(request)
      where request.secondBridgeAddress = L1AssetRouter
      ↓
    Bridgehub calls L1AssetRouter.bridgehubDeposit(chainId, originalCaller, value, data)
      ↓
      AssetRouterBase._burn(chainId, assetId, originalCaller, transferData, ...)
        ↓
        NativeTokenVault.bridgeBurn(chainId, l2MsgValue, assetId, originalCaller, data)
          ↓
          _bridgeBurnNativeToken(...)
            → _depositFunds(originalCaller, ERC20(token), amount)
                balanceBefore = token.balanceOf(NTV)
                token.safeTransferFrom(originalCaller, NTV, amount)
                balanceAfter  = token.balanceOf(NTV)
                assert balanceAfter - balanceBefore == amount
            → _handleChainBalanceIncrease(chainId, assetId, amount)
            → returns bridgeMintData = DataEncoding.encodeBridgeMintData(
                  originalCaller, receiver, token, amount, erc20Metadata)
        ↓
      L1AssetRouter.getDepositCalldata(sender, assetId, bridgeMintData)
        → returns abi.encodeCall(L2AssetRouter.finalizeDeposit,
                                 (L1_CHAIN_ID, assetId, bridgeMintData))
      ↓
      returns L2TransactionRequestTwoBridgesInner {
        l2Contract: L2_ASSET_ROUTER_ADDR,
        l2Calldata: finalizeDeposit calldata above,
        txDataHash: keccak256(encodingVersion || assetId || transferData)
      }
    ↓
  Bridgehub._sendRequest(chainId, ...)
    → IZKChain(zkChain).bridgehubRequestL2Transaction(request)
        enqueues L2 transaction in the chain's Mailbox
        returns canonicalTxHash
  ↓
  Bridgehub calls L1AssetRouter.bridgehubConfirmL2Transaction(
      chainId, txDataHash, canonicalTxHash)
    → records depositHappened[chainId][txDataHash] = canonicalTxHash
```

**What is in-flight after this completes:**
- Tokens are locked inside `NativeTokenVault` on L1
- A pending L2 transaction targeting `L2AssetRouter.finalizeDeposit` is in the Mailbox
- The L2 calldata encodes `amount` via `bridgeMintData`

### L2 deposit finalization (L2 side)

When the ZK chain processes the enqueued L2 transaction:

```
L2 Bootloader executes the enqueued tx:
  → L2AssetRouter.finalizeDeposit(L1_CHAIN_ID, assetId, transferData)
      ↓
      AssetRouterBase._finalizeDeposit(chainId, assetId, transferData, L2_NTV_ADDR)
        ↓
        NativeTokenVault.bridgeMint(chainId, assetId, transferData)
          ↓
          if token is native to L1 (originChainId == L1):
            _bridgeMintNativeToken(chainId, assetId, data)
              (receiver, amount) = DataEncoding.decodeBridgeMintData(data)
              _handleChainBalanceDecrease(chainId, assetId, amount)
              _withdrawFunds(assetId, receiver, token, amount)
                → token.transfer(receiver, amount)   [L2 token]
          else (bridged token):
            _bridgeMintBridgedToken(chainId, assetId, data)
              (receiver, amount) = DataEncoding.decodeBridgeMintData(data)
              _handleChainBalanceDecrease(chainId, assetId, amount)
              IBridgedStandardToken(token).bridgeMint(receiver, amount)
```

**What changes:**
- The in-flight L1→L2 message is consumed (L2 tx executed)
- `amount` tokens are minted or transferred to `receiver` on L2
- `amount` is decoded from the same `bridgeMintData` that was encoded on L1

The amount identity that must be proved:
`amount_locked_in_NTV_on_L1 == amount_minted_to_receiver_on_L2`
where both are the `amount` field from `DataEncoding.encodeBridgeMintData` /
`DataEncoding.decodeBridgeMintData`.

### L2 → L1 withdrawal

The user calls `L2AssetRouter.withdraw` to initiate a withdrawal back to L1.

```
User
  → L2AssetRouter.withdraw(assetId, assetData)
      → _withdrawSender(assetId, assetData, msg.sender, alwaysNewFormat=true)
          ↓
          AssetRouterBase._burn(L1_CHAIN_ID, assetId, originalCaller, transferData, ...)
            ↓
            NativeTokenVault.bridgeBurn(...)   [L2 NTV]
              ↓
              if native token on L2:
                _bridgeBurnNativeToken(...)
                  → _depositFunds(...)  burns/locks L2 tokens
                  → returns bridgeMintData encoding amount
              else (bridged token):
                _bridgeBurnBridgedToken(...)
                  → IBridgedStandardToken(token).bridgeBurn(originalCaller, amount)
                  → returns bridgeMintData encoding amount
          ↓
          message = _getAssetRouterWithdrawMessage(assetId, bridgeMintData)
            = abi.encodePacked(
                finalizeDeposit.selector,   // 4 bytes
                block.chainid,              // L2 chain ID
                assetId,                    // 32 bytes
                bridgeMintData              // encodes amount
              )
          ↓
          txHash = L2ContractHelper.sendMessageToL1(message)
            → emits L2→L1 log; message becomes part of L2 batch state
```

**What is in-flight after this completes:**
- `amount` tokens are burned/locked on L2
- An L2→L1 message is emitted containing `amount` in `bridgeMintData`
- The message settles as part of the next committed L2 batch on L1

### L1 withdrawal finalization

After the L2 batch containing the withdrawal is committed and proved on L1:

```
Anyone
  → L1Nullifier.finalizeWithdrawal(
        chainId, l2BatchNumber, l2MessageIndex, l2TxNumberInBatch,
        message, merkleProof)
      ↓
      verifyWithdrawal(chainId, l2BatchNumber, l2MessageIndex,
                       l2TxNumberInBatch, message, merkleProof)
        → validates Merkle proof against committed L2 batch root
        → confirms message is in the L2 output
      ↓
      assert !s_isWithdrawalFinalized[chainId][batchNumber][msgIndex]
      s_isWithdrawalFinalized[chainId][batchNumber][msgIndex] = true
      ↓
      parseL2WithdrawalMessage(chainId, message)
        → extracts (assetId, transferData)   [transferData encodes amount]
      ↓
      IL1AssetRouter(assetRouter).finalizeDeposit(chainId, assetId, transferData)
        ↓
        AssetRouterBase._finalizeDeposit(chainId, assetId, transferData, NTV_addr)
          ↓
          NativeTokenVault.bridgeMint(chainId, assetId, transferData)   [L1 NTV]
            ↓
            _bridgeMintNativeToken(...)
              (receiver, amount) = DataEncoding.decodeBridgeMintData(transferData)
              _handleChainBalanceDecrease(chainId, assetId, amount)
              _withdrawFunds(assetId, receiver, token, amount)
                → token.transfer(receiver, amount)   [releases L1 tokens from NTV]
```

**What changes:**
- The L2→L1 message is nullified (can never be replayed)
- `amount` tokens are released from `NativeTokenVault` on L1 to `receiver`
- `amount` is the same value that was burned on L2

### Key structural observations

**NativeTokenVault is a shared base contract.** `L1NativeTokenVault` and
`L2NativeTokenVault` both inherit from `NativeTokenVault`. The abstract function
`_withdrawFunds` has different implementations on each side:
- L1: calls `token.safeTransfer(to, amount)` (releases ERC-20 from custody)
- L2: calls the L2 token contract's transfer or `bridgeMint`

The `DataEncoding.encodeBridgeMintData` / `decodeBridgeMintData` pair is the
common message format used on all four legs. The `amount` field is always at
the same position in the encoded bytes. Proving encode/decode round-trips for
this format is the single most important shared lemma across all four paths.

**The in-flight representation is not a single mapping.** It is:
- For L1→L2: the canonical tx in the Mailbox (identified by `canonicalTxHash`)
  and `depositHappened[chainId][txDataHash] = canonicalTxHash` in L1AssetRouter
- For L2→L1: the L2→L1 message log in the committed L2 batch, with
  `s_isWithdrawalFinalized[chainId][batch][index]` as the consumed flag

**The verified function in the existing proofs** (`fun_bridgehubDepositNonBaseTokenAsset`)
corresponds to `L1AssetRouter.bridgehubDeposit` in the Solidity source. The Yul
compiler generates internal function names; the Lean spec targets the full
deposit orchestration in L1AssetRouter that is triggered by the Bridgehub.

---

## Extension: Full System-Level Balance Conservation

### The expanded goal

The current roadmap proves one quarter of a larger theorem. The deposit path shows:

```
L1_custody_before = L1_custody_after + inflight_L1_to_L2_amount
```

The full system-level invariant the project should eventually reach is:

```
L1_custody + inflight_L1_to_L2 + L2_balance + inflight_L2_to_L1 = total_supply
```

where each term is a sum over all tokens and all pending messages, and `total_supply`
is a constant representing the total amount of a given token that has ever been
deposited into the bridge system.

This requires proving four contract paths and composing them into one global
conservation theorem.

### The four contract paths

#### Path 1: L1 deposit initiation (current focus)

Contract: `L1AssetRouter.bridgehubDepositNonBaseTokenAsset`

Effect on the invariant:

- `L1_custody` decreases by `amount`
- `inflight_L1_to_L2` increases by `amount`
- net change: zero

This is what Milestones A through E prove. This path is in progress.

#### Path 2: L2 deposit finalization

Entry point: `L2AssetRouter.finalizeDeposit(chainId, assetId, transferData)`
Delegates to: `NativeTokenVault.bridgeMint` → `_bridgeMintNativeToken` or `_bridgeMintBridgedToken`

Effect on the invariant:

- `inflight_L1_to_L2` decreases by `amount` (L2 tx executed, Mailbox entry consumed)
- `L2_balance` increases by `amount` (tokens minted or transferred to recipient on L2)
- net change: zero

The `amount` is decoded from `transferData` via `DataEncoding.decodeBridgeMintData`.
This is the same bytes blob produced by `NativeTokenVault.bridgeBurn` on L1.

This path is not yet in scope for formal verification. No Yul compilation or VC
generation has been done for L2 contracts.

#### Path 3: L2 withdrawal initiation

Entry point: `L2AssetRouter.withdraw(assetId, assetData)`
Delegates to: `NativeTokenVault.bridgeBurn` (L2 side) → `L2ContractHelper.sendMessageToL1`

Effect on the invariant:

- `L2_balance` decreases by `amount` (tokens burned or locked on L2)
- `inflight_L2_to_L1` increases by `amount` (L2→L1 log emitted encoding `amount`)
- net change: zero

The emitted L2→L1 message encodes:
`finalizeDeposit.selector || chainId || assetId || bridgeMintData`
where `bridgeMintData` contains `amount` via `DataEncoding.encodeBridgeMintData`.

This path is not yet in scope for formal verification.

#### Path 4: L1 withdrawal finalization

Entry point: `L1Nullifier.finalizeWithdrawal(chainId, batch, msgIndex, txNum, message, proof)`
Then calls: `L1AssetRouter.finalizeDeposit` → `NativeTokenVault.bridgeMint` (L1 side) → token release

Effect on the invariant:

- `inflight_L2_to_L1` decreases by `amount` (nullifier set, message can never replay)
- `L1_custody` increases by `amount` (tokens released from NTV to recipient)
- net change: zero

This path has proof scaffolding in place:
- `specs/L1Nullifier/L1Nullifier/fun_finalizeWithdrawal_user.lean`
- `specs/L1Nullifier/L1Nullifier/fun_verifyWithdrawal_user.lean`
- `specs/L1Nullifier/L1Nullifier/fun_parseL2WithdrawalMessage_user.lean`

However the abstract specs are all `sorry`. The skeleton is ready for proof work.

### Modeling the in-flight state

The in-flight components are not stored in a single contract variable but are implicit
in pending messages and nullifier sets. At the proof level they must be modeled
abstractly.

For `inflight_L1_to_L2`:

- a deposit enqueues an L2 tx in the chain's Mailbox
- the tx calldata is `L2AssetRouter.finalizeDeposit(chainId, assetId, bridgeMintData)`
- `amount` is embedded in `bridgeMintData` via `DataEncoding.encodeBridgeMintData`
- on-chain it is tracked by `depositHappened[chainId][txDataHash] = canonicalTxHash`
  in `L1AssetRouter`
- abstractly: the multiset of `amount` values in all Mailbox entries not yet finalized

For `inflight_L2_to_L1`:

- a withdrawal emits an L2→L1 log via `L2ContractHelper.sendMessageToL1`
- the message encodes `finalizeDeposit.selector || chainId || assetId || bridgeMintData`
- `amount` is embedded in `bridgeMintData` via `DataEncoding.encodeBridgeMintData`
- on-chain: the message is consumed once by setting
  `s_isWithdrawalFinalized[chainId][batch][index] = true` in `L1Nullifier`
- abstractly: the multiset of `amount` values in all committed-but-not-yet-finalized
  withdrawal messages

At the system level, the invariant does not require tracking the full message structure.
It only requires tracking the `amount` field embedded in each message. The encoding
lemmas (Milestones A and C) exist precisely to expose that field.

### Suggested abstract invariant shape

```lean
def TotalBridgeSupplyPreserved
    (total_supply : Literal)
    (l1_custody : Literal)
    (inflight_l1_to_l2 : Multiset Literal)
    (l2_balance : Literal)
    (inflight_l2_to_l1 : Multiset Literal) : Prop :=
  l1_custody + inflight_l1_to_l2.sum + l2_balance + inflight_l2_to_l1.sum = total_supply
```

Each of the four contract paths is then a lemma that:

- takes `TotalBridgeSupplyPreserved` as a precondition
- applies the relevant contract function
- concludes `TotalBridgeSupplyPreserved` still holds on the updated state

The `total_supply` term is a ghost quantity: it does not appear in any contract
storage, but it is provably constant because each path moves `amount` from one term
to another without changing the sum.

### New milestones

#### Milestone F: L1 withdrawal finalization proof

Goal:

- prove that `fun_finalizeWithdrawal` in L1Nullifier implies:
  - the withdrawal message is nullified (consumed exactly once)
  - the extracted amount equals the amount in the L2 log
  - L1 custody increases by that amount

The full call chain for this path is:
`L1Nullifier.finalizeWithdrawal`
  → `L1Nullifier.verifyWithdrawal` (Merkle proof check)
  → `L1Nullifier.parseL2WithdrawalMessage` (extract assetId + transferData)
  → `L1AssetRouter.finalizeDeposit` (dispatch to asset handler)
  → `NativeTokenVault.bridgeMint` on L1 → `_bridgeMintNativeToken`
  → `_withdrawFunds` → `token.safeTransfer(receiver, amount)`

Required sub-lemmas:

- `A_fun_parseL2WithdrawalMessage`: extract the exact `amount` from `bridgeMintData`
  in the L2→L1 message (uses `DataEncoding.decodeBridgeMintData`)
- `A_fun_verifyWithdrawal`: prove Merkle proof check does not alter `amount`
- `A_fun_finalizeDeposit` (L1 side): prove dispatch to NTV preserves `amount`
- `A_fun_bridgeMint` (L1 NTV): prove `amount` tokens are released to `receiver`
- `A_fun_finalizeWithdrawal`: compose all the above

Acceptance criteria:

- `fun_finalizeWithdrawal_user` proves an amount equality of the form:
  `extracted_amount = L1_custody_after - L1_custody_before`
- the nullifier `s_isWithdrawalFinalized[chainId][batch][index]` is set in the
  output state (double-spend prevention)
- theorem builds with no `sorry`

Dependencies from current roadmap:

- Milestone F does not depend on Milestones A–E
- it can be developed in parallel on the L1Nullifier proof files

#### Milestone G: L2 contract pipeline setup

Goal:

- bring L2 contracts into the Clear verification pipeline

The L2 contracts live in `era-contracts/l1-contracts/contracts/bridge/` (the repo
uses a single contracts tree). The two L2-side entry points to verify are:
- `L2AssetRouter.finalizeDeposit` (deposit finalization)
- `L2AssetRouter.withdraw` / `_withdrawSender` (withdrawal initiation)
- `NativeTokenVault.bridgeMint` (shared base, L2 instantiation)
- `NativeTokenVault.bridgeBurn` (shared base, L2 instantiation)

Work:

1. Compile `L2AssetRouter.sol` and `L2NativeTokenVault.sol` to Yul using `solc`
2. Run the VC generator to produce `_gen.lean` and `_user.lean` stubs
3. Confirm the generated files build as identity stubs before writing proofs

This is infrastructure work, not proof work. No Lean proofs are written at this stage.

Acceptance criteria:

- `generated/L2AssetRouter/` and `generated/L2NativeTokenVault/` directories exist with VC files
- `specs/L2AssetRouter/` and `specs/L2NativeTokenVault/` stubs build as identity abstractions
- `lakefile.lean` includes the new modules

#### Milestone H: L2 deposit finalization and withdrawal initiation proofs

Goal:

- prove amount preservation through `L2AssetRouter.finalizeDeposit` and
  `L2AssetRouter.withdraw`

For deposit finalization (`L2AssetRouter.finalizeDeposit → NTV.bridgeMint`):

- `DataEncoding.decodeBridgeMintData` extracts the exact `amount` that was encoded
  by `DataEncoding.encodeBridgeMintData` on L1 (shared encoding, round-trip lemma)
- the token transfer to `receiver` moves exactly `amount` tokens
- the amount identity links to what `fun_getDepositCalldata` encoded (Milestone C)

For withdrawal initiation (`L2AssetRouter.withdraw → NTV.bridgeBurn → sendMessageToL1`):

- `NTV.bridgeBurn` burns/locks exactly `amount` tokens from the caller on L2
- `_getAssetRouterWithdrawMessage` encodes `amount` into the L2→L1 message via
  `DataEncoding.encodeBridgeMintData`
- the emitted message is what `L1Nullifier.parseL2WithdrawalMessage` will later decode

Acceptance criteria:

- `A_fun_finalizeDeposit` (L2): proves `L2_balance_after = L2_balance_before + amount`
  where `amount` is decoded from `transferData` by `decodeBridgeMintData`
- `A_fun_withdraw` (L2): proves `L2_balance_after = L2_balance_before - amount` and
  the emitted L2→L1 message encodes `amount` via `encodeBridgeMintData`
- the encode/decode round-trip lemma for `DataEncoding` is proved once and shared
  across all four paths

#### Milestone I: global conservation theorem

Goal:

- compose all four path lemmas into the global `TotalBridgeSupplyPreserved` invariant

Shape of each component lemma:

```
deposit_preserves_total :
  TotalBridgeSupplyPreserved total l1 flights_in l2 flights_out →
  bridgehubDepositNonBaseTokenAsset amount ... →
  TotalBridgeSupplyPreserved total (l1 - amount) (flights_in + {amount}) l2 flights_out

l2_finalize_preserves_total :
  TotalBridgeSupplyPreserved total l1 flights_in l2 flights_out →
  amount ∈ flights_in →
  bridgeMint amount ... →
  TotalBridgeSupplyPreserved total l1 (flights_in - {amount}) (l2 + amount) flights_out

l2_withdraw_preserves_total :
  TotalBridgeSupplyPreserved total l1 flights_in l2 flights_out →
  bridgeBurn amount ... →
  TotalBridgeSupplyPreserved total l1 flights_in (l2 - amount) (flights_out + {amount})

l1_finalize_preserves_total :
  TotalBridgeSupplyPreserved total l1 flights_in l2 flights_out →
  amount ∈ flights_out →
  finalizeWithdrawal amount ... →
  TotalBridgeSupplyPreserved total (l1 + amount) flights_in l2 (flights_out - {amount})
```

The global theorem is that repeated application of any sequence of these four steps
leaves `total_supply` unchanged.

Acceptance criteria:

- all four component lemmas stated and proved
- `TotalBridgeSupplyPreserved` invariant defined in a shared file
- a top-level theorem states invariant preservation under all four operations
- no `sorry`

### Dependency order for the extension

The new milestones can be pursued in parallel with the existing roadmap:

```
Current roadmap (A → B → C → D → E)    Milestone F (independent)
                           ↓                      ↓
                     Milestone G (infrastructure for L2 contracts)
                           ↓
                     Milestone H (L2 bridgeMint + bridgeBurn proofs)
                           ↓
                     Milestone I (global composition)
```

Milestone F (L1Nullifier finalization proof) does not depend on Milestones A–E and can
be worked on immediately in parallel.

Milestones G and H require the L2 contract pipeline, which is new infrastructure work
and can begin as soon as someone is ready to invest time in the tooling setup.

Milestone I requires all previous milestones and is the final integration step.

### Scope note

The full global invariant (Milestone I) requires trusting certain things that are hard
or impossible to verify directly in the Clear framework:

- the L2 Merkle proof verification (used in `fun_verifyWithdrawal`) is ultimately trusted
  by `L1Nullifier` to encode the correct amount from the L2 log
- the ZK proof system itself, which proves correct L2 state transition

These can be treated as axioms or assumptions in the global theorem. The theorem would
then read: "assuming the ZK proof is sound and the Merkle proof is correct, the total
value is conserved across all four contract paths."

This is an appropriate scope for smart contract formal verification. The ZK soundness
is a separate cryptographic argument, not a contract-level argument.

### Updated definition of done for the full system theorem

We should consider the expanded goal reached only when all of the following are true:

- Milestones A through E are complete (L1 deposit path)
- Milestone F is complete (L1 withdrawal finalization)
- Milestones G and H are complete (L2 pipeline and proofs)
- `TotalBridgeSupplyPreserved` is defined with all four components
- all four path lemmas are proved
- the global invariant theorem builds with no `sorry` under the stated ZK/Merkle
  axioms
