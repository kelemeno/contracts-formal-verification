import specs.AtomicFlowManager.AtomicFlowManager.no_double_refund_user

/-
  READABLE VOCABULARY for the AtomicFlowManager leg state machine.

  `no_double_refund_user.lean` proves the refund path's key results in raw model
  terms — a leg's state is a packed byte read as `Fin.land (evm.sload slot) 255`
  and compared against numerals.  This file names the enum and the accessor so
  the results read as statements about leg states.

  Same discipline as `specs/InteropHandler/Layout.lean`: each restatement is
  `exact`-ed from the raw theorem with no unfolding, so the kernel checks that the
  named form is the same proposition, and the raw versions remain what was proved.

  ENUM, verified against era-contracts at pin c67894b97
  (`l1-contracts/contracts/atomic-interop/IAtomicInterop.sol:17`):

      enum LegState { Unset, Committed, Revertable, Reverted }

  so `Unset = 0`, `Committed = 1`, `Revertable = 2`, `Reverted = 3`.
-/

namespace AtomicFlowManager.Layout

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
open OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
open AtomicFlowManager.Common generated.AtomicFlowManager.AtomicFlowManager

/-! ## The `LegState` enum -/

/-- The low-byte mask for a packed `enum` field. -/
def STATE_MASK : UInt256 := 255

/-- `LegState.Unset = 0` — no commitment recorded for this leg. -/
def Unset : UInt256 := 0

/-- `LegState.Committed = 1` — the leg is committed and still live. -/
def Committed : UInt256 := 1

/-- `LegState.Revertable = 2` — `authorizeRefund` has accepted a timeout proof,
so a refund may now be claimed. -/
def Revertable : UInt256 := 2

/-- `LegState.Reverted = 3` — the refund has been paid out. -/
def Reverted : UInt256 := 3

/-- Read a leg's packed state byte out of its `_state[flowId][bundleHash]` slot. -/
def legStateOf (evm : EVMState) (slot : UInt256) : UInt256 :=
  Fin.land (evm.sload slot) STATE_MASK

/-! ## The refund path, restated -/

/-- **A REFUNDED LEG CANNOT BE REFUNDED AGAIN** (readable form of
`reclaim_after_refund_reverts`).

After the refund write has set the leg's state byte to `Reverted`, re-running
`claimRefund`'s check on the SAME slot reverts.  Combined with the other
instances of `refund_check_reverts` (which reject `Unset` and `Committed`),
`claimRefund` can pay out only a leg in state `Revertable` — i.e. only after
`authorizeRefund`'s timeout proof, and at most once.

This is the AtomicFlowManager's no-double-refund guarantee: the point at which
funds actually move, so a second payout would be a direct theft. -/
theorem refunded_leg_cannot_refund_again
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {slot : Literal} {s_set s_mid s₉ : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hset_exec : execCall (fuel+1)
        update_storage_value_offset_enum_LegState_to_enum_LegState_7877 []
        (Ok evm store, [slot]) = s_set)
    (hcheck_exec : exec (fuel+1) block_5412558363375237105
        ((Ok s_set.evm store)⟦"split_expr_21" ↦ slot⟧) = s_mid)
    (hif_exec : exec (fuel+1) if_880639588767859599 s_mid = s₉) :
    s₉.evm.reverted = true :=
  reclaim_after_refund_reverts hacc hset_exec hcheck_exec hif_exec

/-- **THE REFUND WRITE SETS THE STATE TO `Reverted`** (readable form of
`update_storage_sets_reverted_byte`): after the refund write, the leg's state
byte reads exactly `Reverted`, which is what makes the guard above fire. -/
theorem refund_write_sets_reverted
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    {slot : Literal} {s_set : State}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome)
    (hset_exec : execCall (fuel+1)
        update_storage_value_offset_enum_LegState_to_enum_LegState_7877 []
        (Ok evm store, [slot]) = s_set) :
    legStateOf s_set.evm slot = Reverted :=
  update_storage_sets_reverted_byte hacc hset_exec

end AtomicFlowManager.Layout
