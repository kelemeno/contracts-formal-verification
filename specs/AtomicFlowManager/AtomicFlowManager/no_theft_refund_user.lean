import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective
import specs.KeccakDistinct
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5412558363375237105
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3729329767271556662
import specs.AtomicFlowManager.AtomicFlowManager.no_double_refund_user

/-
  NO THEFT VIA THE FAILED-DEPOSIT (REFUND) PATH — hash/slot binding.

  `claimRefund(flowId, bundleBytes)` recomputes
  `bundleHash = keccak256(abi.encode(sourceChainId, bundleBytes))` and gates the
  payout on `_state[flowId][bundleHash] == Revertable`.  The theft question is:
  can an attacker submit CRAFTED bundle bytes (different receiver / amount /
  calls) and ride an authorization that was granted for the honest bundle?

  The state machine already gives (axiom-free, `no_double_refund_user.lean`):
  a claim pays out only from `Revertable`, and at most once.  What remains is
  the BINDING between the authorization and the exact bundle bytes.  This file
  proves the slot-separation half:

  * `accessor_slots_differ_of_key_ne` — the 2-level `_state` accessor maps
    DIFFERENT bundle hashes (same flow) to DIFFERENT storage slots.  Hence an
    authorization written at the honest bundle's slot is invisible to the
    crafted bundle's CHECK: the crafted slot is `Unset(0)`, and by
    `refund_check_reverts` the crafted claim REVERTS.

  Trusted base: this uses `Clear.KeccakInjective.keccak256_inj` (A6′ — distinct
  preimages ⇒ distinct slots, the standard collision-resistance idealization).
  The remaining half of the binding — different bundle BYTES ⇒ different
  `bundleHash` (injectivity through `abi.encode`) — is the same idealization
  applied to the variable-length encode and is tracked separately.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective
     AtomicFlowManager.Common

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-- Word-0 read-back on the accessor scratch: the second `mstore` (at 32)
cannot touch `[0, 32)`, and the first round-trips. -/
private lemma accessor_word0
    (σ : EVMState) (key base : UInt256) :
    ((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory 0 = key := by
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h0v : ((0 : UInt256)).val = 0 := by decide
  rw [show ((σ.mstore 0 key).mstore 32 base).machine_state
      = (σ.machine_state.updateMemory 0 key).updateMemory 32 base from rfl]
  rw [lookupMemory_updateMemory_outside _ 32 base 0 (by rw [h32v]; try norm_num)
      (by rw [h0v]; try norm_num) (by left; rw [h0v, h32v]; try norm_num)]
  exact lookupMemory_updateMemory_self' _ 0 key (by rw [h0v]; try norm_num)

/-- The first element of the 64-byte accessor interval is the word at 0. -/
private lemma accInterval_head
    (σ : EVMState) (key base : UInt256) :
    (accInterval σ key base).get? 0
      = some (((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory 0) := by
  unfold accInterval EVMState.mkInterval
  have h0 : ((0 : UInt256)).val = 0 := by decide
  have h64 : ((64 : UInt256)).val = 64 := by decide
  rw [h0, h64]
  rfl

/-- **Accessor preimage separation**: different keys give different 64-byte
accessor intervals (they differ at word 0). -/
lemma accInterval_ne_of_key_ne
    {σ₁ σ₂ : EVMState} {k₁ k₂ base₁ base₂ : UInt256}
    (hne : k₁ ≠ k₂) :
    accInterval σ₁ k₁ base₁ ≠ accInterval σ₂ k₂ base₂ := by
  intro he
  have h := congrArg (fun l => l.get? 0) he
  simp only [accInterval_head, accessor_word0] at h
  exact hne (Option.some.inj h)

/-- **SLOT SEPARATION (A6′).** The `_state[flowId][bundleHash]` accessor maps
different bundle hashes to DIFFERENT storage slots: an authorization
(`Revertable`) written at the honest bundle's slot cannot be read by a claim
for any other bundle hash.  Uses the keccak-injectivity idealization. -/
theorem accessor_slots_differ_of_key_ne
    {σ₁ σ₂ : EVMState} {k₁ k₂ base₁ base₂ : UInt256}
    {r₁ r₂ : UInt256} {e₁ e₂ : EVMState}
    (hne : k₁ ≠ k₂)
    (h₁ : accOut σ₁ k₁ base₁ = (r₁, e₁))
    (h₂ : accOut σ₂ k₂ base₂ = (r₂, e₂))
    (hclean₁ : e₁.hash_collision = false)
    (hclean₂ : e₂.hash_collision = false) :
    r₁ ≠ r₂ := by
  have hs₁ : ((σ₁.mstore 0 k₁).mstore 32 base₁).keccak256 0 64
      = some (r₁, e₁) := by
    have := keccakOut_some_of_clean (σ := (σ₁.mstore 0 k₁).mstore 32 base₁)
      (p := 0) (n := 64) (by rw [show keccakOut ((σ₁.mstore 0 k₁).mstore 32 base₁) 0 64
        = accOut σ₁ k₁ base₁ from rfl, h₁]; exact hclean₁)
    rw [show keccakOut ((σ₁.mstore 0 k₁).mstore 32 base₁) 0 64
        = accOut σ₁ k₁ base₁ from rfl, h₁] at this
    exact this
  have hs₂ : ((σ₂.mstore 0 k₂).mstore 32 base₂).keccak256 0 64
      = some (r₂, e₂) := by
    have := keccakOut_some_of_clean (σ := (σ₂.mstore 0 k₂).mstore 32 base₂)
      (p := 0) (n := 64) (by rw [show keccakOut ((σ₂.mstore 0 k₂).mstore 32 base₂) 0 64
        = accOut σ₂ k₂ base₂ from rfl, h₂]; exact hclean₂)
    rw [show keccakOut ((σ₂.mstore 0 k₂).mstore 32 base₂) 0 64
        = accOut σ₂ k₂ base₂ from rfl, h₂] at this
    exact this
  exact keccak256_inj hs₁ hs₂ (accInterval_ne_of_key_ne hne)

/-- **NO THEFT VIA CRAFTED BUNDLE BYTES (A6′).** Suppose the honest bundle's
hash `k₁` resolves (via the `_state` accessor) to slot `r₁`, and an
authorization is granted by writing any value at `r₁` (the
`authorizeRefund` SET).  For ANY other bundle hash `k₂ ≠ k₁` whose leg was
`Unset` before the authorization, the crafted `claimRefund` still REVERTS:
the accessor maps `k₂` to a DIFFERENT slot `r₂ ≠ r₁` (keccak injectivity),
the authorization write is invisible at `r₂` (storage non-aliasing), the
crafted leg stays `Unset(0) ≠ Revertable(2)`, and the CHECK + guard-if end
`reverted = true`.  An attacker cannot ride an honest authorization with
substituted bundle bytes — the payout is bound to the exact committed hash. -/
theorem crafted_claim_reverts_after_authorization
    {σ₁ σ₂ : EVMState} {k₁ k₂ base₁ base₂ : UInt256}
    {r₁ r₂ : UInt256} {e₁ e₂ : EVMState}
    {evm : EVMState} {w : UInt256} {store : VarStore}
    {fuel : ℕ} {s_mid s₉ : State}
    -- the two accessor computations (honest and crafted), both collision-free
    (hne : k₂ ≠ k₁)
    (h₁ : accOut σ₁ k₁ base₁ = (r₁, e₁))
    (h₂ : accOut σ₂ k₂ base₂ = (r₂, e₂))
    (hclean₁ : e₁.hash_collision = false)
    (hclean₂ : e₂.hash_collision = false)
    -- the crafted leg was Unset before the honest authorization
    (hunset : Fin.land (evm.sload r₂) 255 = 0)
    -- the crafted CHECK runs on the post-authorization storage (write at r₁)
    (hslot : (Ok (evm.sstore r₁ w) store)["split_expr_21"]!! = r₂)
    (hcheck : exec (fuel+1) block_5412558363375237105 (Ok (evm.sstore r₁ w) store) = s_mid)
    (hif : exec (fuel+1) if_3729329767271556662 s_mid = s₉) :
    s₉.evm.reverted = true := by
  -- the crafted slot differs from the authorized slot
  have hr : r₂ ≠ r₁ := accessor_slots_differ_of_key_ne hne h₂ h₁ hclean₂ hclean₁
  -- the authorization write is invisible at the crafted slot
  have hsl : (evm.sstore r₁ w).sload r₂ = evm.sload r₂ :=
    Clear.KeccakDistinct.sload_sstore_of_ne evm hr
  -- the crafted leg is still Unset: valid (< 4) and not Revertable (≠ 2)
  exact refund_check_reverts hslot
    (by rw [hsl, hunset]; decide)
    (by rw [hsl, hunset]; decide)
    hcheck hif

end

end generated.AtomicFlowManager.AtomicFlowManager
