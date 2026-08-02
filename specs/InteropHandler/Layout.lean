import specs.InteropHandler.InteropHandler.fun_verifyBundle_user
import specs.KeccakDeterminism
import specs.InteropHandler.InteropHandler.exec_allowed_user

/-
  READABLE VOCABULARY for the InteropHandler memory layout.

  The gate theorems in `fun_verifyBundle_user.lean` are stated in raw model
  terms, e.g.

      Fin.land (evm.mload (evm.mload (P + 96) + 32))
        (Fin.shiftLeft 1 160 - 1) ≠ 65549

  which is precise but forces every reader to re-derive the struct offsets.
  This file names the pieces so the same statement reads as

      asAddress (proofSender evm P) ≠ L2_INTEROP_CENTER_ADDR

  A DELIBERATE TRADE-OFF.  Naming moves trust from the theorem statement to
  these definitions: a reviewer who reads only the restated theorem no longer
  sees the offsets and must instead trust the accessors below.  Each definition
  is therefore justified against the Solidity source, and each restated theorem
  is proved by `exact`-ing the raw one, so the two forms are definitionally the
  same statement — the raw version remains available and is what was actually
  proved.

  LAYOUT, verified against era-contracts at pin c67894b97:

  `MessageInclusionProof` (`l1-contracts/contracts/common/Messaging.sol:316`)
      chainId         offset   0
      l1BatchNumber   offset  32
      l2MessageIndex  offset  64
      message         offset  96   ← a struct field, so in memory a POINTER
      proof           offset 128

  `L2Message` (`Messaging.sol:41`)
      txNumberInBatch offset   0   (uint16, padded to a full word)
      sender          offset  32
      data            offset  64

  `L2_INTEROP_CENTER_ADDR` (`common/l2-helpers/L2ContractAddresses.sol:128`)
      = BUILT_IN_CONTRACTS_OFFSET + 0x0d = 0x1000D = 65549
-/

namespace InteropHandler.Layout

open Clear Clear.KeccakDeterminism EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
open InteropHandler.Common generated.InteropHandler.InteropHandler

/-! ## Address arithmetic -/

/-- The EVM's 160-bit address mask, `2^160 - 1`, as the compiler builds it
(`sub(shl(160, 1), 1)`). -/
def ADDR_MASK : UInt256 := Fin.shiftLeft (1 : UInt256) 160 - 1

/-- Truncate a word to an address (the `and(x, 2^160 - 1)` cleanup Solidity
emits whenever a word is used as an `address`). -/
def asAddress (x : UInt256) : UInt256 := Fin.land x ADDR_MASK

/-- `L2_INTEROP_CENTER_ADDR = 0x1000D`, the canonical interop center. -/
def L2_INTEROP_CENTER_ADDR : UInt256 := 65549

/-! ## `MessageInclusionProof` / `L2Message` accessors -/

/-- The `message` field of a `MessageInclusionProof` at memory pointer `P`
(offset 96).  Being a struct field it holds a POINTER to the `L2Message`. -/
def proofMessage (evm : EVMState) (P : UInt256) : UInt256 := evm.mload (P + 96)

/-- The `sender` field of an `L2Message` at memory pointer `M` (offset 32). -/
def messageSender (evm : EVMState) (M : UInt256) : UInt256 := evm.mload (M + 32)

/-- The declared sender of the message carried by the proof at `P`: follow the
`message` pointer, then read its `sender` field. -/
def proofSender (evm : EVMState) (P : UInt256) : UInt256 :=
  messageSender evm (proofMessage evm P)

/-! ## The gate theorems, restated

Each is `exact`-ed from the raw version in `fun_verifyBundle_user.lean`, so the
vocabulary adds readability without adding trust: they are the same proposition
up to unfolding. -/

/-- **NO VERIFICATION ON A FOREIGN MESSAGE SENDER** (readable form of
`unauthorized_sender_reverts`).

If the proof's declared message sender, truncated to an address, is not the
canonical interop center, then running the compiled prologue of `_verifyBundle`
ends reverted.

Contrapositive: a bundle can only reach the `Verified` write on a message whose
sender field is `L2_INTEROP_CENTER_ADDR` — the sole authentication of a
cross-chain bundle, so forging a delivery requires impersonating the interop
center itself. -/
theorem unauthorized_sender_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s₉ : State} {P : Literal}
    (hP : (Ok evm store)["var_proof_mpos"]!! = P)
    (hbad : asAddress (proofSender evm P) ≠ L2_INTEROP_CENTER_ADDR)
    (hexec : exec (fuel+1) (.Block
        [block_2731350847861160598, block_6357692007766190094,
         block_2808946740468959641, if_4527419366897270229]) (Ok evm store) = s₉) :
    s₉.evm.reverted = true :=
  generated.InteropHandler.InteropHandler.unauthorized_sender_reverts hP hbad hexec

/-! ## Bundle status: the packed low byte of a status slot -/

/-- The low-byte mask Solidity uses for a packed `uint8` status field. -/
def STATUS_MASK : UInt256 := 255

/-- `BundleStatus.Verified = 1`. -/
def Verified : UInt256 := 1

/-- Read the packed status byte out of a full storage word. -/
def statusOf (evm : EVMState) (slot : UInt256) : UInt256 :=
  Fin.land (evm.sload slot) STATUS_MASK

/-- Clear the low status byte of `w` and set it to `st` — the clear-then-set
idiom the compiler emits for writing a packed `uint8` field. -/
def setStatus (w st : UInt256) : UInt256 :=
  Fin.lor (Fin.land w (Clear.UInt256.lnot STATUS_MASK)) st

/-! ## The status-write results, restated -/

/-- **THE VERIFY WRITE MARKS THE BUNDLE VERIFIED** (readable form composed from
`verify_write_block` and `verified_status_reads_one`).

Running the compiled status-write block leaves the bundle's status slot reading
exactly `Verified`.  This is the state effect that `unauthorized_sender_reverts`
and `not_included_reverts` gate: the two revert results say the write is
unreachable without the canonical sender and a positive inclusion answer, and
this says what the write does when it is reached. -/
theorem verify_write_marks_verified
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {d : Literal}
    (hd : (Ok evm store)["dataSlot"]!! = d)
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome) :
    statusOf (exec (fuel+1) block_4779748611206726122 (Ok evm store)).evm d = Verified := by
  unfold statusOf STATUS_MASK Verified
  rw [generated.InteropHandler.InteropHandler.verify_write_block hd]
  exact generated.InteropHandler.InteropHandler.verified_status_reads_one hacc

/-- **NO VERIFICATION WITHOUT INCLUSION** (readable form of
`not_included_reverts`): when the decoded answer of the `_proveInclusion`
staticcall is zero, the gate reverts (`MessageNotIncluded`). -/
theorem not_included_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h : (Ok evm store)["expr"]!! = 0) :
    (exec (fuel+1) if_7459957530221088163 (Ok evm store)).evm.reverted = true :=
  generated.InteropHandler.InteropHandler.not_included_reverts h

/-! ## Mapping-slot derivation -/

/-- The storage slot of `m[key]` for a mapping declared at slot `base`: the
Solidity rule `keccak256(key ‖ base)`, computed via the scratch space at
offsets 0 and 32.  This is exactly `accOut`'s value component, so every
determinism and cache-agreement lemma proved for `accOut` applies to it. -/
def mappingSlot (evm : EVMState) (key base : UInt256) : UInt256 :=
  (accOut evm key base).1

/-- `bundleStatus` is declared at slot 1, so the status word for `bh` lives at
`keccak256(bh ‖ 1)`. -/
def bundleStatusSlot (evm : EVMState) (bh : UInt256) : UInt256 :=
  mappingSlot evm bh 1

/-- **THE SLOT BLOCK DERIVES THE BUNDLE-STATUS SLOT** (readable form of
`verify_slot_block`).  The compiled derivation block binds `dataSlot` to exactly
the storage slot of `bundleStatus[bh]`, and advances the EVM to `accOut`'s
post-state (carrying the two scratch writes and the keccak cache update). -/
theorem slot_block_derives_bundleStatusSlot
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bh : Literal}
    (hbh : (Ok evm store)["var__bundleHash"]!! = bh) :
    exec (fuel+1) block_8249276522053995858 (Ok evm store)
      = Ok (accOut evm bh 1).2
          (((store.insert "dataSlot" (bundleStatusSlot evm bh)).insert
              "cleaned_1" 0).insert "cleaned_1" 0) :=
  generated.InteropHandler.InteropHandler.verify_slot_block hbh

/-! ## The composite: what `_verifyBundle`'s status path actually does -/

/-- Reading back the slot the derivation block just bound.  The two `cleaned_1`
writes sit above `dataSlot` in the store, so the lookup skips them. -/
private lemma lookup_dataSlot
    {E : EVMState} {store : VarStore} {v : UInt256} :
    (Ok E (((store.insert "dataSlot" v).insert "cleaned_1" 0).insert
        "cleaned_1" 0))["dataSlot"]!! = v := by
  unfold State.lookup!
  dsimp only
  rw [Finmap.lookup_insert_of_ne _ (by decide),
      Finmap.lookup_insert_of_ne _ (by decide),
      Finmap.lookup_insert]
  rfl

/-- **THE STATUS PATH MARKS THE BUNDLE VERIFIED** — the fully readable
end-to-end statement of `_verifyBundle`'s state effect.

Running the mapping-slot derivation block and then the status-write block leaves
`bundleStatus[bh]` reading exactly `Verified`.

Read together with the two revert gates, this is the whole story of the
function's status path:

* `unauthorized_sender_reverts` — unreachable unless the proof's message sender
  is the canonical interop center;
* `not_included_reverts` — unreachable without a positive inclusion answer;
* this theorem — and when reached, `bundleStatus[bh]` becomes `Verified`. -/
theorem verify_path_marks_bundle_verified
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bh : Literal}
    (hbh : (Ok evm store)["var__bundleHash"]!! = bh)
    (hacc : (((accOut evm bh 1).2).lookupAccount
        ((accOut evm bh 1).2).execution_env.code_owner).isSome) :
    statusOf (exec (fuel+1) block_4779748611206726122
        (exec (fuel+1) block_8249276522053995858 (Ok evm store))).evm
      (bundleStatusSlot evm bh) = Verified := by
  rw [slot_block_derives_bundleStatusSlot hbh]
  exact verify_write_marks_verified lookup_dataSlot hacc

/-! ## Execution authorization

`exec_allowed_user.lean` proves the two accepting cases of the authorization
block separately (`auth_self_pass`, `auth_executor_pass`).  Naming the predicate
lets them be stated as one theorem about one condition. -/

/-- `caller()` — the immediate sender of the current call. -/
def caller (evm : EVMState) : UInt256 := (evm.execution_env.source : UInt256)

/-- `address()` — the handler contract itself. -/
def self (evm : EVMState) : UInt256 := (evm.execution_env.code_owner : UInt256)

/-- The call came from the handler itself (a re-entrant self-call). -/
def IsSelfCall (evm : EVMState) : Prop := caller evm = self evm

/-- The bundle's declared execution chain is acceptable: either it names the
current chain, or it is the CHAIN-AGNOSTIC `0`, which any chain may execute. -/
def ChainAllows (evm : EVMState) (C : UInt256) : Prop :=
  C = evm.chainId ∨ C = 0

/-- The bundle's declared executor address (masked to 160 bits) is the caller. -/
def ExecutorIsCaller (evm : EVMState) (A : UInt256) : Prop :=
  asAddress A = caller evm

/-- **THE AUTHORIZATION CONDITION.**  Execution of a restricted bundle is
permitted exactly when the caller is the handler itself, or the bundle's declared
(chain, executor) pair designates this caller on this chain. -/
def AuthorizedExecutor (evm : EVMState) (C A : UInt256) : Prop :=
  IsSelfCall evm ∨ (ChainAllows evm C ∧ ExecutorIsCaller evm A)

/-- **THE AUTHORIZATION CASE SPLIT.**  Decomposes `AuthorizedExecutor` into the
exact two shapes the proved pass-theorems consume. -/
theorem authorized_cases {evm : EVMState} {C A : UInt256}
    (hauth : AuthorizedExecutor evm C A) :
    IsSelfCall evm
      ∨ (¬ IsSelfCall evm ∧ ChainAllows evm C ∧ ExecutorIsCaller evm A) := by
  by_cases hself : IsSelfCall evm
  · exact Or.inl hself
  · rcases hauth with hs | ⟨hc, he⟩
    · exact absurd hs hself
    · exact Or.inr ⟨hself, hc, he⟩

/-- **AUTHORIZED CALLERS PASS THE GATE.**  One theorem for the whole accepting
surface of the executor gate, composed from `auth_self_pass` and
`auth_executor_pass`: if `AuthorizedExecutor` holds of the parsed
`(chainId, executor)` pair, the authorization block computes `expr = 1` and
leaves the EVM untouched.

Read with `unauthorized_sender_reverts`, this is the positive half of the
access-control story — that theorem says an unauthenticated message cannot reach
the verified write; this one says exactly which callers the executor gate
admits. -/
theorem authorized_passes
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {C A : Literal}
    (hC : (Ok evm store)["expr_287_component"]!! = C)
    (hA : (Ok evm store)["expr_component"]!! = A)
    (hauth : AuthorizedExecutor evm C A) :
    ∃ σ' : VarStore,
      exec (fuel+1) generated.InteropHandler.InteropHandler.authBlk (Ok evm store)
        = Ok evm σ'
      ∧ (Ok evm σ')["expr"]!! = 1 := by
  rcases authorized_cases hauth with hs | ⟨hns, hc, he⟩
  · exact generated.InteropHandler.InteropHandler.auth_self_pass hs
  · exact generated.InteropHandler.InteropHandler.auth_executor_pass hC hA hns hc he

end InteropHandler.Layout
