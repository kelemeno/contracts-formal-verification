import Clear.ReasoningPrinciple
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- The state the bounds guard sees: parameters bound, length loaded, comparison made. -/
def arrIdxGuardState (array index : Literal) (s₀ : State) : State :=
  let f := s₀☎️⟦["array", "index"],[array, index]⟧
  let g := f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  g⟦"split_expr_1" ↦ (decide (g["index"]!! < (g["split_expr_0"]!!))).toUInt256⟧

/-- The state after the element address is computed: `keccak(array) + index`, offset 0. -/
def arrIdxResultState (ss : State) : State :=
  let m := ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧
  let kk := Clear.State.multifill ["split_expr_2"] (primCall m .Keccak256 [0, 32]).2
    (primCall m .Keccak256 [0, 32]).1
  let sl := kk⟦"slot" ↦ kk["split_expr_2"]!! + (kk["index"]!!)⟧
  sl⟦"offset" ↦ 0⟧

/-- **Address of element `index` of a dynamic storage array.**

```
    split_expr_0 := sload(array)              -- the length
    if iszero(lt(index, split_expr_0)) { panic_error_0x32() }   -- bounds check
    mstore(0, array); split_expr_2 := keccak256(0, 32)          -- base = keccak(slot)
    slot := add(split_expr_2, index)
    offset := 0
```

Solidity's dynamic-array layout: elements live at `keccak(arraySlot) + index`, and the
bounds check is against the CURRENT length read from the array's own slot.  `offset := 0`
because a `bytes32` fills its word — no packing.

The two intermediate states are NAMED rather than inline `let`s, so value lemmas can talk
about them; a spec whose intermediates are anonymous can only be proved equal to the code,
not reasoned about. -/
def A_storage_array_index_access_bytes32_dyn_ptr (slot offset : Identifier)
    (array index : Literal) (s₀ s₉ : State) : Prop :=
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_2600721580863995212
      (arrIdxGuardState array index s₀) ss ∧
    s₉ = 🧟(arrIdxResultState ss)🏪⟦s₀⟧⟦offset ↦ (arrIdxResultState ss)["offset"]!!⟧⟦slot ↦
      (arrIdxResultState ss)["slot"]!!⟧

lemma storage_array_index_access_bytes32_dyn_ptr_abs_of_concrete {s₀ s₉ : State} {slot offset array index} :
  Spec (storage_array_index_access_bytes32_dyn_ptr_concrete_of_code.1 slot offset array index) s₀ s₉ →
  Spec (A_storage_array_index_access_bytes32_dyn_ptr slot offset array index) s₀ s₉ := by
  unfold storage_array_index_access_bytes32_dyn_ptr_concrete_of_code A_storage_array_index_access_bytes32_dyn_ptr
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma storage_array_index_access_bytes32_dyn_ptr_isOk {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  -- normalise BOTH sides: the simp set strips the return's inserts and the two the
  -- body itself made, so `hoo` has to be pushed through it as well
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma storage_array_index_access_bytes32_dyn_ptr_not_break {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (storage_array_index_access_bytes32_dyn_ptr_isOk hnf h)

/-- **`initcall` preserves the evm** for this call's parameter list. -/
lemma initcall_evm_ai {s : State} {a i : Literal} (h : isOk s) :
    (s☎️⟦["array", "index"],[a, i]⟧).evm = s.evm := by
  rcases s with ⟨evm, store⟩ | _ | _
  · simp only [State.initcall, multifill_cons, multifill_nil, evm_insert, evm_setStore]
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- **The bounds flag, in the caller's terms.**

`split_expr_1` is `lt(index, sload(array))` computed on the initcall'd state; recovering
the parameters turns it into the caller's own comparison.  This is the step that lets a
caller of the accessor know WHICH comparison decides the panic. -/
lemma index_flag_val {s₀ : State} {array index : Literal} (hok : isOk s₀) :
    (((s₀☎️⟦["array", "index"],[array, index]⟧)⟦"split_expr_0" ↦
        Clear.EVMState.sload (s₀☎️⟦["array", "index"],[array, index]⟧).evm
          ((s₀☎️⟦["array", "index"],[array, index]⟧)["array"]!!)⟧)["index"]!!)
      < (((s₀☎️⟦["array", "index"],[array, index]⟧)⟦"split_expr_0" ↦
        Clear.EVMState.sload (s₀☎️⟦["array", "index"],[array, index]⟧).evm
          ((s₀☎️⟦["array", "index"],[array, index]⟧)["array"]!!)⟧)["split_expr_0"]!!)
    ↔ index < Clear.EVMState.sload s₀.evm array := by
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  rw [lookup_insert_of_ne (by decide), lookup_insert' hf,
    Clear.lookup_initcall_snd hok (by decide), Clear.lookup_initcall_fst hok,
    initcall_evm_ai hok]

/-- The guard's flag, on the named guard state. -/
lemma arrIdxGuardState_flag {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardState array index s₀)["split_expr_1"]!!
      = (decide (index < Clear.EVMState.sload s₀.evm array)).toUInt256 := by
  unfold arrIdxGuardState
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  rw [lookup_insert' (by simpa [isOk_insert] using hf)]
  congr 1
  rw [lookup_insert_of_ne (by decide), lookup_insert' hf,
    Clear.lookup_initcall_snd hok (by decide), Clear.lookup_initcall_fst hok,
    initcall_evm_ai hok]

/-- The guard state keeps the caller's evm. -/
lemma arrIdxGuardState_evm {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardState array index s₀).evm = s₀.evm := by
  unfold arrIdxGuardState
  simp only [evm_insert]
  exact initcall_evm_ai hok

/-- The guard state still carries the caller's `array` argument. -/
lemma arrIdxGuardState_array {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardState array index s₀)["array"]!! = array := by
  unfold arrIdxGuardState
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  exact Clear.lookup_initcall_fst hok

/-- …and its `index` argument. -/
lemma arrIdxGuardState_index {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardState array index s₀)["index"]!! = index := by
  unfold arrIdxGuardState
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  exact Clear.lookup_initcall_snd hok (by decide)

/-- `arrIdxResultState` is out of fuel only if its input is. -/
lemma isOutOfFuel_arrIdxResultState {ss : State} : ❓ (arrIdxResultState ss) ↔ ❓ ss := by
  unfold arrIdxResultState
  simp only [isOutOfFuel_insert', isOutOfFuel_multifill', primCall_keccakOut,
    isOutOfFuel_setEvm']

/-- `arrIdxResultState` preserves `Ok`. -/
lemma isOk_arrIdxResultState {ss : State} (h : isOk ss) : isOk (arrIdxResultState ss) := by
  unfold arrIdxResultState
  simp only [isOk_insert, primCall_keccakOut]
  exact isOk_multifill (by simpa [isOk_setEvm] using h)

/-  **NEXT: the slot equation.**

    s₉[slot]!! = (keccakOut ((s₀.evm).mstore 0 array) 0 32).1 + index

given `index < sload s₀.evm array`.  Everything it needs is now proved above:
`arrIdxGuardState_flag` (the guard is the identity when the check passes),
`arrIdxGuardState_evm/_array/_index` (the caller's arguments and evm survive into the
guard state), `isOk_arrIdxResultState` and `isOutOfFuel_arrIdxResultState` (the side
conditions), and `primCall_keccakOut` (the keccak bridge).

The assembly gets as far as

    multifill ["split_expr_2"] (primCall M .Keccak256 [0,32]).2 (…).1 ["split_expr_2"]!!
      + (…)["index"]!!  =  (keccakOut (mstore s₀.evm 0 array) 0 32).1 + index

and then needs the two lookups read off the reduced multifill.  The rewrite that keeps
failing is the `["index"]!!` one: after `lookup_insert_of_ne` the remaining term is not
the `s🇪⟦e⟧[v]!!` shape `Clear.lookup_setEvm` expects.  Reading that goal with `trace_state`
and matching the shape exactly is the way in -- the same method that settled every other
step here.
-/


end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
