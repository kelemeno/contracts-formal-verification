import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective

/-
  FLOW-ID BINDING (A6′) — the flowId pins the deadline and the settlement
  layer.

  `_checkFlowId` recomputes `flowId = keccak256(abi.encode(legBundleHashes,
  legSourceChainIds, deadline, settlementLayerChainId))` (#37).  The compiled
  encoder writes the two STATIC heads LAST — the masked deadline at
  `headStart+64` and the settlement-layer chain id at `headStart+96` — and
  the keccak runs from `headStart`.  By the pinning principle (#43), two
  encodings with the SAME hash agree at every fixed offset; here we extract
  offsets 64/96 through the encoder's top two writes: **equal flowIds carry
  equal deadlines and equal settlement layers** — no tail reasoning needed.

  Composed with #37 (the gates accept only matching flowIds) and #33 (every
  commit value bakes the flowId in): the deadline that every temporal guard
  (#36) compares against, and the settlement-layer clock it reads, are
  bound — per leg, through the tree commitment — to the values fixed at
  deposit time.  A flow cannot be re-presented with a stretched deadline or
  a different clock.

  Trusted base: A6′ (`keccak256_inj`) via the pinning theorems.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

private lemma val_add_lit {P q : UInt256} {c : ℕ} (hq : q.val = c)
    (hbound : P.val + c < 2 ^ 256) : (P + q).val = P.val + c := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  rw [Fin.val_add, hq]
  exact Nat.mod_eq_of_lt (by omega)

private lemma finOfNat_self (x : UInt256) : (Fin.ofNat x.val : UInt256) = x := by
  apply Fin.ext
  have hv : (Fin.ofNat x.val : UInt256).val = x.val % UInt256.size := rfl
  rw [hv, Nat.mod_eq_of_lt x.isLt]

private lemma mkInterval_get?
    (ms : MachineState) (p n : UInt256) (j : ℕ) (hj : j < n.val) :
    (EVMState.mkInterval ms p n).get? j
      = some (ms.lookupMemory (Fin.ofNat (p.val + j))) := by
  unfold EVMState.mkInterval
  rw [List.get?_map, List.get?_map, List.get?_range' _ _ hj]
  simp only [Option.map_some', one_mul]

/-- The deadline word reads back at `h+64` through the final `h+96` write. -/
private lemma head64_readback
    {E : EVMState} {h w sl : UInt256}
    (hh : h.val + 128 ≤ 2 ^ 256) :
    ((E.mstore (h + 64) w).mstore (h + 96) sl).machine_state.lookupMemory (h + 64)
      = w := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have hP64 : (h + 64).val = h.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (h + 96).val = h.val + 96 := val_add_lit h96v (by omega)
  show ((E.machine_state.updateMemory (h + 64) w).updateMemory (h + 96) sl).lookupMemory (h + 64)
      = w
  rw [lookupMemory_updateMemory_outside _ (h + 96) sl (h + 64)
      (by omega) (by omega) (by left; omega)]
  exact lookupMemory_updateMemory_self' _ (h + 64) w (by omega)

/-- The settlement-layer word reads back at `h+96` (the last write). -/
private lemma head96_readback
    {E : EVMState} {h w sl : UInt256}
    (hh : h.val + 128 ≤ 2 ^ 256) :
    ((E.mstore (h + 64) w).mstore (h + 96) sl).machine_state.lookupMemory (h + 96)
      = sl := by
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have hP96 : (h + 96).val = h.val + 96 := val_add_lit h96v (by omega)
  show ((E.machine_state.updateMemory (h + 64) w).updateMemory (h + 96) sl).lookupMemory (h + 96)
      = sl
  exact lookupMemory_updateMemory_self' _ (h + 96) sl (by omega)

/-- **FLOW-ID BINDING (A6′).**  Two flow encodings — each of the compiled
shape, ending with the masked deadline at `h+64` and the settlement layer at
`h+96` — that hash to the SAME flowId carry the SAME deadline word and the
SAME settlement layer (and the same encoding length: same leg count). -/
theorem flowid_pins_deadline_sl
    {E₁ E₂ σ₁' σ₂' : EVMState} {h₁ h₂ n₁ n₂ w₁ w₂ sl₁ sl₂ r : UInt256}
    (hk₁ : ((E₁.mstore (h₁ + 64) w₁).mstore (h₁ + 96) sl₁).keccak256 h₁ n₁
        = some (r, σ₁'))
    (hk₂ : ((E₂.mstore (h₂ + 64) w₂).mstore (h₂ + 96) sl₂).keccak256 h₂ n₂
        = some (r, σ₂'))
    (hh₁ : h₁.val + 128 ≤ 2 ^ 256) (hh₂ : h₂.val + 128 ≤ 2 ^ 256)
    (hn₁ : 96 < n₁.val) (hn₂ : 96 < n₂.val) :
    w₁ = w₂ ∧ sl₁ = sl₂ ∧ n₁ = n₂ := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  -- element 64 on each side is the deadline word
  have e₁64 : (EVMState.mkInterval
      ((E₁.mstore (h₁ + 64) w₁).mstore (h₁ + 96) sl₁).machine_state h₁ n₁).get? 64
      = some w₁ := by
    rw [mkInterval_get? _ _ _ 64 (by omega)]
    rw [show h₁.val + 64 = (h₁ + 64).val from (val_add_lit h64v (by omega)).symm,
        finOfNat_self]
    rw [head64_readback hh₁]
  have e₂64 : (EVMState.mkInterval
      ((E₂.mstore (h₂ + 64) w₂).mstore (h₂ + 96) sl₂).machine_state h₂ n₂).get? 64
      = some w₂ := by
    rw [mkInterval_get? _ _ _ 64 (by omega)]
    rw [show h₂.val + 64 = (h₂ + 64).val from (val_add_lit h64v (by omega)).symm,
        finOfNat_self]
    rw [head64_readback hh₂]
  -- element 96 on each side is the settlement layer
  have e₁96 : (EVMState.mkInterval
      ((E₁.mstore (h₁ + 64) w₁).mstore (h₁ + 96) sl₁).machine_state h₁ n₁).get? 96
      = some sl₁ := by
    rw [mkInterval_get? _ _ _ 96 (by omega)]
    rw [show h₁.val + 96 = (h₁ + 96).val from (val_add_lit h96v (by omega)).symm,
        finOfNat_self]
    rw [head96_readback hh₁]
  have e₂96 : (EVMState.mkInterval
      ((E₂.mstore (h₂ + 64) w₂).mstore (h₂ + 96) sl₂).machine_state h₂ n₂).get? 96
      = some sl₂ := by
    rw [mkInterval_get? _ _ _ 96 (by omega)]
    rw [show h₂.val + 96 = (h₂ + 96).val from (val_add_lit h96v (by omega)).symm,
        finOfNat_self]
    rw [head96_readback hh₂]
  refine ⟨?_, ?_, keccak256_same_out_length_eq hk₁ hk₂⟩
  · have h := keccak256_same_out_word_eq hk₁ hk₂ 64
    rw [e₁64, e₂64] at h
    exact Option.some.inj h
  · have h := keccak256_same_out_word_eq hk₁ hk₂ 96
    rw [e₁96, e₂96] at h
    exact Option.some.inj h

end

end generated.AtomicFlowManager.AtomicFlowManager
