import specs.InteropHandler.InteropHandler.fun_verifyBundle_user

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

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
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

end InteropHandler.Layout
