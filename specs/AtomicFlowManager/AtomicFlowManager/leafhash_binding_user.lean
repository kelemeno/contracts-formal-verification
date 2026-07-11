import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective
import specs.AtomicFlowManager.AtomicFlowManager.imt_leafhash_user

/-
  LEAF-HASH BINDING (A6′) — the leaf hash pins the leaf FIELDS.

  `hashLeafOut` (#26's leaf hash) hashes the 96-byte scratch region holding the
  three IMT leaf fields `(key, nextIndex, nextKey)`.  This file proves the
  injectivity direction: **two collision-free leaf hashes with the same output
  have the same three field values** (`hashLeafOut_inj`) — extracted from the
  keccak preimage at region offsets 0/32/64.

  Combined with `foldRoot_binding` (#27): for a committed root, a tree position
  determines the leaf hash, and the leaf hash determines the decoded fields —
  so the value delivered/witnessed at any proven position is unique.  This is
  the field-level binding needed by both gates (#25's commit-value check reads
  field 0; #26's adjacency window reads fields 0 and 2).

  Trusted base: `Clear.KeccakInjective.keccak256_inj` (A6′).
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

/-- `Fin.ofNat` of an in-range value is the value. -/
private lemma finOfNat_self (x : UInt256) : (Fin.ofNat x.val : UInt256) = x := by
  apply Fin.ext
  have hv : (Fin.ofNat x.val : UInt256).val = x.val % UInt256.size := rfl
  rw [hv, Nat.mod_eq_of_lt x.isLt]

/-! ## Symbolic element extraction from `mkInterval` -/

/-- Element `j` of `mkInterval ms p n` is the word read at byte `p + j`. -/
private lemma mkInterval_get?
    (ms : MachineState) (p n : UInt256) (j : ℕ) (hj : j < n.val) :
    (EVMState.mkInterval ms p n).get? j
      = some (ms.lookupMemory (Fin.ofNat (p.val + j))) := by
  unfold EVMState.mkInterval
  rw [List.get?_map, List.get?_map, List.get?_range' _ _ hj]
  simp only [Option.map_some', one_mul]

/-! ## Field read-back from the leaf scratch -/

/-- Field 0 (`leaf.key`) reads back at `P+32`. -/
private lemma leafScratch_field0
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (leafScratchEvm evm leaf).machine_state.lookupMemory (evm.mload 64 + 32)
      = evm.mload leaf := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  have hP64 : (P + 64).val = P.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (P + 96).val = P.val + 96 := val_add_lit h96v (by omega)
  rw [show (leafScratchEvm evm leaf).machine_state
      = ((((evm.machine_state.updateMemory (P + 32) (evm.mload leaf)).updateMemory
          (P + 64) (evm.mload (leaf + 32))).updateMemory
          (P + 96) (evm.mload (leaf + 64))).updateMemory
          P 96).updateMemory 64 (P + 128) from rfl]
  rw [lookupMemory_updateMemory_outside _ 64 (P + 128) (P + 32)
      (by rw [h64v]; norm_num) (by omega) (by right; rw [h64v]; omega)]
  rw [lookupMemory_updateMemory_outside _ P 96 (P + 32)
      (by omega) (by omega) (by right; omega)]
  rw [lookupMemory_updateMemory_outside _ (P + 96) _ (P + 32)
      (by omega) (by omega) (by left; omega)]
  rw [lookupMemory_updateMemory_outside _ (P + 64) _ (P + 32)
      (by omega) (by omega) (by left; omega)]
  exact lookupMemory_updateMemory_self' _ (P + 32) _ (by omega)

/-- Field 1 (`leaf.nextIndex`) reads back at `P+64`. -/
private lemma leafScratch_field1
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (leafScratchEvm evm leaf).machine_state.lookupMemory (evm.mload 64 + 64)
      = evm.mload (leaf + 32) := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  have hP64 : (P + 64).val = P.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (P + 96).val = P.val + 96 := val_add_lit h96v (by omega)
  rw [show (leafScratchEvm evm leaf).machine_state
      = ((((evm.machine_state.updateMemory (P + 32) (evm.mload leaf)).updateMemory
          (P + 64) (evm.mload (leaf + 32))).updateMemory
          (P + 96) (evm.mload (leaf + 64))).updateMemory
          P 96).updateMemory 64 (P + 128) from rfl]
  rw [lookupMemory_updateMemory_outside _ 64 (P + 128) (P + 64)
      (by rw [h64v]; norm_num) (by omega) (by right; rw [h64v]; omega)]
  rw [lookupMemory_updateMemory_outside _ P 96 (P + 64)
      (by omega) (by omega) (by right; omega)]
  rw [lookupMemory_updateMemory_outside _ (P + 96) _ (P + 64)
      (by omega) (by omega) (by left; omega)]
  exact lookupMemory_updateMemory_self' _ (P + 64) _ (by omega)

/-- Field 2 (`leaf.nextKey`) reads back at `P+96`. -/
private lemma leafScratch_field2
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (leafScratchEvm evm leaf).machine_state.lookupMemory (evm.mload 64 + 96)
      = evm.mload (leaf + 64) := by
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h96v : ((96 : UInt256)).val = 96 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  have hP64 : (P + 64).val = P.val + 64 := val_add_lit h64v (by omega)
  have hP96 : (P + 96).val = P.val + 96 := val_add_lit h96v (by omega)
  rw [show (leafScratchEvm evm leaf).machine_state
      = ((((evm.machine_state.updateMemory (P + 32) (evm.mload leaf)).updateMemory
          (P + 64) (evm.mload (leaf + 32))).updateMemory
          (P + 96) (evm.mload (leaf + 64))).updateMemory
          P 96).updateMemory 64 (P + 128) from rfl]
  rw [lookupMemory_updateMemory_outside _ 64 (P + 128) (P + 96)
      (by rw [h64v]; norm_num) (by omega) (by right; rw [h64v]; omega)]
  rw [lookupMemory_updateMemory_outside _ P 96 (P + 96)
      (by omega) (by omega) (by right; omega)]
  exact lookupMemory_updateMemory_self' _ (P + 96) _ (by omega)

/-! ## Preimage-interval extraction at the three field offsets -/

/-- The hash preimage interval of `hashLeaf`: element 0 is field 0. -/
private lemma leafInterval_get0
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (EVMState.mkInterval (leafScratchEvm evm leaf).machine_state
        (evm.mload 64 + 32) 96).get? 0
      = some (evm.mload leaf) := by
  have h96v : ((96 : UInt256)).val = 96 := by decide
  rw [mkInterval_get? _ _ _ 0 (by rw [h96v]; norm_num)]
  rw [Nat.add_zero, finOfNat_self]
  rw [leafScratch_field0 hp hplow]

/-- Element 32 is field 1. -/
private lemma leafInterval_get32
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (EVMState.mkInterval (leafScratchEvm evm leaf).machine_state
        (evm.mload 64 + 32) 96).get? 32
      = some (evm.mload (leaf + 32)) := by
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  rw [mkInterval_get? _ _ _ 32 (by rw [h96v]; norm_num)]
  rw [show (P + 32).val + 32 = (P + 64).val from by
    rw [hP32, val_add_lit h64v (by omega)]]
  rw [finOfNat_self]
  rw [leafScratch_field1 hp hplow]

/-- Element 64 is field 2. -/
private lemma leafInterval_get64
    {evm : EVMState} {leaf : Literal}
    (hp : (evm.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow : 96 ≤ (evm.mload 64).val) :
    (EVMState.mkInterval (leafScratchEvm evm leaf).machine_state
        (evm.mload 64 + 32) 96).get? 64
      = some (evm.mload (leaf + 64)) := by
  have h96v : ((96 : UInt256)).val = 96 := by decide
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have h32v : ((32 : UInt256)).val = 32 := by decide
  set P := evm.mload 64 with hPdef
  have hP32 : (P + 32).val = P.val + 32 := val_add_lit h32v (by omega)
  rw [mkInterval_get? _ _ _ 64 (by rw [h96v]; norm_num)]
  rw [show (P + 32).val + 64 = (P + 96).val from by
    rw [hP32, val_add_lit h96v (by omega)]]
  rw [finOfNat_self]
  rw [leafScratch_field2 hp hplow]

/-! ## The injectivity theorem -/

/-- **LEAF-HASH BINDING (A6′).**  Two collision-free `hashLeafOut` computations
with the SAME hash output agree on all three leaf fields
`(key, nextIndex, nextKey)`. -/
theorem hashLeafOut_inj
    {σ₁ σ₂ : EVMState} {leaf₁ leaf₂ : Literal}
    {r : UInt256} {e₁ e₂ : EVMState}
    (h₁ : hashLeafOut σ₁ leaf₁ = (r, e₁))
    (h₂ : hashLeafOut σ₂ leaf₂ = (r, e₂))
    (hclean₁ : e₁.hash_collision = false)
    (hclean₂ : e₂.hash_collision = false)
    (hp₁ : (σ₁.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow₁ : 96 ≤ (σ₁.mload 64).val)
    (hp₂ : (σ₂.mload 64).val + 128 ≤ 18446744073709551615)
    (hplow₂ : 96 ≤ (σ₂.mload 64).val) :
    σ₁.mload leaf₁ = σ₂.mload leaf₂
      ∧ σ₁.mload (leaf₁ + 32) = σ₂.mload (leaf₂ + 32)
      ∧ σ₁.mload (leaf₁ + 64) = σ₂.mload (leaf₂ + 64) := by
  rw [hashLeafOut_length hp₁ hplow₁] at h₁
  rw [hashLeafOut_length hp₂ hplow₂] at h₂
  have hs₁ : (leafScratchEvm σ₁ leaf₁).keccak256 (σ₁.mload 64 + 32) 96
      = some (r, e₁) := by
    have := keccakOut_some_of_clean (σ := leafScratchEvm σ₁ leaf₁)
      (p := σ₁.mload 64 + 32) (n := 96) (by rw [h₁]; exact hclean₁)
    rw [h₁] at this
    exact this
  have hs₂ : (leafScratchEvm σ₂ leaf₂).keccak256 (σ₂.mload 64 + 32) 96
      = some (r, e₂) := by
    have := keccakOut_some_of_clean (σ := leafScratchEvm σ₂ leaf₂)
      (p := σ₂.mload 64 + 32) (n := 96) (by rw [h₂]; exact hclean₂)
    rw [h₂] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    refine keccak256_inj hs₁ hs₂ ?_ rfl
    intro he
    have h := congrArg (fun l => l.get? 0) he
    simp only [leafInterval_get0 hp₁ hplow₁, leafInterval_get0 hp₂ hplow₂] at h
    exact hne (Option.some.inj h)
  · by_contra hne
    refine keccak256_inj hs₁ hs₂ ?_ rfl
    intro he
    have h := congrArg (fun l => l.get? 32) he
    simp only [leafInterval_get32 hp₁ hplow₁, leafInterval_get32 hp₂ hplow₂] at h
    exact hne (Option.some.inj h)
  · by_contra hne
    refine keccak256_inj hs₁ hs₂ ?_ rfl
    intro he
    have h := congrArg (fun l => l.get? 64) he
    simp only [leafInterval_get64 hp₁ hplow₁, leafInterval_get64 hp₂ hplow₂] at h
    exact hne (Option.some.inj h)

end

end generated.AtomicFlowManager.AtomicFlowManager
