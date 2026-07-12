import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective
import specs.CalldatacopyFrame

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


/-! ### The leg-count word — read back through both copies -/

/-- The full flow-encode tower (heads, two length-prefixed copies, final
static heads) reads the FIRST array's length word back at `h+128`. -/
private lemma legcount_readback
    {σ : EVMState} {h len₁ len₂ w₁ Dm sl start₁ start₂ c₁ c₂ t₁ : UInt256}
    (hh : h.val + 160 ≤ 2 ^ 256)
    (ht₁ : h.val + 160 ≤ t₁.val)
    (ht₁nw : t₁.val + 32 < 2 ^ 256)
    (hb₁ : h.val + 160
        + (ByteArray.extractBytes start₁.val c₁.val σ.execution_env.input_data).size
        + 31 ≤ 2 ^ 256)
    (hb₂ : t₁.val + 32
        + (ByteArray.extractBytes start₂.val c₂.val σ.execution_env.input_data).size
        + 31 ≤ 2 ^ 256) :
    ((((((((σ.mstore h 128).mstore (h + 128) len₁).calldatacopy (h + 160) start₁ c₁).mstore
        (h + 32) w₁).mstore t₁ len₂).calldatacopy (t₁ + 32) start₂ c₂).mstore
        (h + 64) Dm).mstore (h + 96) sl).machine_state.lookupMemory (h + 128)
      = len₁ := by
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have h128v : ((128 : UInt256)).val = 128 := by decide
  have h160v : ((160 : UInt256)).val = 160 := by decide
  have e32 : (h + 32).val = h.val + 32 := val_add_lit h32v (by omega)
  have e64 : (h + 64).val = h.val + 64 := val_add_lit h64v (by omega)
  have e96 : (h + 96).val = h.val + 96 := val_add_lit h96v (by omega)
  have e128 : (h + 128).val = h.val + 128 := val_add_lit h128v (by omega)
  have e160 : (h + 160).val = h.val + 160 := val_add_lit h160v (by omega)
  have et32 : (t₁ + 32).val = t₁.val + 32 := val_add_lit h32v (by omega)
  -- peel the two final head writes
  show ((((((((σ.mstore h 128).mstore (h + 128) len₁).calldatacopy (h + 160) start₁ c₁).mstore
      (h + 32) w₁).mstore t₁ len₂).calldatacopy (t₁ + 32) start₂ c₂).machine_state.updateMemory
      (h + 64) Dm).updateMemory (h + 96) sl).lookupMemory (h + 128) = len₁
  rw [lookupMemory_updateMemory_outside _ (h + 96) sl (h + 128)
      (by omega) (by omega) (by right; omega)]
  rw [lookupMemory_updateMemory_outside _ (h + 64) Dm (h + 128)
      (by omega) (by omega) (by right; omega)]
  -- the second copy sits entirely above
  rw [Clear.CalldatacopyFrame.lookupMemory_calldatacopy_below
      (by omega)
      (by
        simp only [Clear.CalldatacopyFrame.execution_env_mstore,
                   Clear.CalldatacopyFrame.execution_env_calldatacopy]
        omega)]
  -- the second length word and the pointer head sit outside
  show (((((σ.mstore h 128).mstore (h + 128) len₁).calldatacopy (h + 160) start₁ c₁).machine_state.updateMemory
      (h + 32) w₁).updateMemory t₁ len₂).lookupMemory (h + 128) = len₁
  rw [lookupMemory_updateMemory_outside _ t₁ len₂ (h + 128)
      (by omega) (by omega) (by left; omega)]
  rw [lookupMemory_updateMemory_outside _ (h + 32) w₁ (h + 128)
      (by omega) (by omega) (by right; omega)]
  -- the first copy sits above the length word
  rw [Clear.CalldatacopyFrame.lookupMemory_calldatacopy_below
      (by omega)
      (by
        simp only [Clear.CalldatacopyFrame.execution_env_mstore]
        omega)]
  -- the length word itself
  show ((σ.machine_state.updateMemory h 128).updateMemory (h + 128) len₁).lookupMemory (h + 128)
      = len₁
  exact lookupMemory_updateMemory_self' _ (h + 128) len₁ (by omega)

/-- **LEG-COUNT BINDING (A6′).**  Two flow encodings of the full compiled
tower shape hashing to the SAME flowId carry the SAME leg-count word. -/
theorem flowid_pins_legcount
    {σ₁ σ₂ σ₁' σ₂' : EVMState}
    {h₁ h₂ n₁ n₂ l₁ l₂ m₁ m₂ w₁ w₂ D₁ D₂ s₁ s₂ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ t₁ t₂ r : UInt256}
    (hk₁ : ((((((((σ₁.mstore h₁ 128).mstore (h₁ + 128) l₁).calldatacopy (h₁ + 160) a₁ c₁).mstore
        (h₁ + 32) w₁).mstore t₁ m₁).calldatacopy (t₁ + 32) b₁ d₁).mstore
        (h₁ + 64) D₁).mstore (h₁ + 96) s₁).keccak256 h₁ n₁ = some (r, σ₁'))
    (hk₂ : ((((((((σ₂.mstore h₂ 128).mstore (h₂ + 128) l₂).calldatacopy (h₂ + 160) a₂ c₂).mstore
        (h₂ + 32) w₂).mstore t₂ m₂).calldatacopy (t₂ + 32) b₂ d₂).mstore
        (h₂ + 64) D₂).mstore (h₂ + 96) s₂).keccak256 h₂ n₂ = some (r, σ₂'))
    (hh₁ : h₁.val + 160 ≤ 2 ^ 256) (hh₂ : h₂.val + 160 ≤ 2 ^ 256)
    (ht₁ : h₁.val + 160 ≤ t₁.val) (ht₂ : h₂.val + 160 ≤ t₂.val)
    (ht₁nw : t₁.val + 32 < 2 ^ 256) (ht₂nw : t₂.val + 32 < 2 ^ 256)
    (hb₁ : h₁.val + 160
        + (ByteArray.extractBytes a₁.val c₁.val σ₁.execution_env.input_data).size
        + 31 ≤ 2 ^ 256)
    (hb₁' : t₁.val + 32
        + (ByteArray.extractBytes b₁.val d₁.val σ₁.execution_env.input_data).size
        + 31 ≤ 2 ^ 256)
    (hb₂ : h₂.val + 160
        + (ByteArray.extractBytes a₂.val c₂.val σ₂.execution_env.input_data).size
        + 31 ≤ 2 ^ 256)
    (hb₂' : t₂.val + 32
        + (ByteArray.extractBytes b₂.val d₂.val σ₂.execution_env.input_data).size
        + 31 ≤ 2 ^ 256)
    (hn₁ : 128 < n₁.val) (hn₂ : 128 < n₂.val) :
    l₁ = l₂ := by
  have h128v : ((128 : UInt256)).val = 128 := by decide
  have e₁ : (EVMState.mkInterval
      ((((((((σ₁.mstore h₁ 128).mstore (h₁ + 128) l₁).calldatacopy (h₁ + 160) a₁ c₁).mstore
        (h₁ + 32) w₁).mstore t₁ m₁).calldatacopy (t₁ + 32) b₁ d₁).mstore
        (h₁ + 64) D₁).mstore (h₁ + 96) s₁).machine_state h₁ n₁).get? 128
      = some l₁ := by
    rw [mkInterval_get? _ _ _ 128 (by omega)]
    rw [show h₁.val + 128 = (h₁ + 128).val from (val_add_lit h128v (by omega)).symm,
        finOfNat_self]
    rw [legcount_readback hh₁ ht₁ ht₁nw hb₁ hb₁']
  have e₂ : (EVMState.mkInterval
      ((((((((σ₂.mstore h₂ 128).mstore (h₂ + 128) l₂).calldatacopy (h₂ + 160) a₂ c₂).mstore
        (h₂ + 32) w₂).mstore t₂ m₂).calldatacopy (t₂ + 32) b₂ d₂).mstore
        (h₂ + 64) D₂).mstore (h₂ + 96) s₂).machine_state h₂ n₂).get? 128
      = some l₂ := by
    rw [mkInterval_get? _ _ _ 128 (by omega)]
    rw [show h₂.val + 128 = (h₂ + 128).val from (val_add_lit h128v (by omega)).symm,
        finOfNat_self]
    rw [legcount_readback hh₂ ht₂ ht₂nw hb₂ hb₂']
  have h := keccak256_same_out_word_eq hk₁ hk₂ 128
  rw [e₁, e₂] at h
  exact Option.some.inj h

end

end generated.AtomicFlowManager.AtomicFlowManager
