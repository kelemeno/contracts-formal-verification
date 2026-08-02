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

end InteropHandler.Layout
