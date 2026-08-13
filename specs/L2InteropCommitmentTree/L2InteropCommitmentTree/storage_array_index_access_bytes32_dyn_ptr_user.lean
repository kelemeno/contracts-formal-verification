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

/-- **Address of element `index` of a dynamic storage array.**

```
    split_expr_0 := sload(array)              -- the length
    if iszero(lt(index, split_expr_0)) { panic_error_0x32() }   -- bounds check
    mstore(0, array); split_expr_2 := keccak256(0, 32)           -- base = keccak(slot)
    slot := add(split_expr_2, index)
    offset := 0
```

Solidity's dynamic-array layout: elements live at `keccak(arraySlot) + index`, and
the bounds check is against the CURRENT length read from the array's own slot.
`offset := 0` because a `bytes32` fills its word — no packing.

Note the keccak window here is 32 bytes (the slot alone), unlike the mapping
derivations' 64 (key and slot). -/
def A_storage_array_index_access_bytes32_dyn_ptr (slot offset : Identifier) (array index : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array", "index"],[array, index]⟧
  let g := f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  let gc := g⟦"split_expr_1" ↦ (decide (g["index"]!! < g["split_expr_0"]!!)).toUInt256⟧
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_2600721580863995212 gc ss ∧
    (let m := ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧
     let kk := Clear.State.multifill ["split_expr_2"] (primCall m .Keccak256 [0, 32]).2
       (primCall m .Keccak256 [0, 32]).1
     let sl := kk⟦"slot" ↦ kk["split_expr_2"]!! + (kk["index"]!!)⟧
     let of := sl⟦"offset" ↦ 0⟧
     s₉ = 🧟of🏪⟦s₀⟧⟦offset ↦ of["offset"]!!⟧⟦slot ↦ of["slot"]!!⟧)

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

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
