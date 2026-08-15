import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6945705467323769142
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_5303_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Address of element 0** of a dynamic storage array: the no-index specialisation.

```
    if iszero(sload(array)) { panic_error_0x32() }
    mstore(0, array); slot := keccak256(0, 32); offset := 0
```

Same layout rule as the indexed accessor -- elements start at `keccak(arraySlot)` --
but with no `+ index`, so this is element 0 and the bounds check degenerates to "the
array is non-empty". -/
def A_storage_array_index_access_bytes32_dyn_ptr_5303 (slot offset : Identifier) (array : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array"],[array]⟧
  let g := f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_6945705467323769142 g ss ∧
    (let m := ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧
     let kk := Clear.State.multifill ["slot"] (primCall m .Keccak256 [0, 32]).2
       (primCall m .Keccak256 [0, 32]).1
     let of := kk⟦"offset" ↦ 0⟧
     s₉ = 🧟of🏪⟦s₀⟧⟦offset ↦ of["offset"]!!⟧⟦slot ↦ of["slot"]!!⟧)

lemma storage_array_index_access_bytes32_dyn_ptr_5303_abs_of_concrete {s₀ s₉ : State} {slot offset array} :
  Spec (storage_array_index_access_bytes32_dyn_ptr_5303_concrete_of_code.1 slot offset array) s₀ s₉ →
  Spec (A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array) s₀ s₉ := by
  unfold storage_array_index_access_bytes32_dyn_ptr_5303_concrete_of_code A_storage_array_index_access_bytes32_dyn_ptr_5303
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

lemma storage_array_index_access_bytes32_dyn_ptr_5303_isOk {slot offset : Identifier} {array : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma storage_array_index_access_bytes32_dyn_ptr_5303_not_break {slot offset : Identifier} {array : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (storage_array_index_access_bytes32_dyn_ptr_5303_isOk hnf h)


/-- **FRAME.**  The specialised accessor (array slot inlined) writes only `slot` and
`offset`, like its general sibling -- so `var_index` and `var_maxNodeNumber` cross the leaf
write untouched and reach the loop. -/
lemma storage_array_index_access_bytes32_dyn_ptr_5303_frame
    {slot offset : Identifier} {array : Literal} {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hvs : v ≠ slot) (hvo : v ≠ offset)
    (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) :
    s₉[v]!! = s₀[v]!! := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 ((ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧
      |> fun m => Clear.State.multifill ["slot"] (primCall m .Keccak256 [0, 32]).2
           (primCall m .Keccak256 [0, 32]).1)⟦"offset" ↦ 0⟧)) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hvs, lookup_insert_of_ne hvo, Clear.lookup_setStore hrev hok]

/-! The index-zero accessor: it hashes the array slot and returns `keccak(array)` itself,
with no `+ index`.  Same shape as the general variant, so the frames read the same -- the
guard preserves everything, then one `mstore` and one hash. -/

private lemma resultOf_evm {ss : State} (hok : isOk ss) :
    (Clear.State.multifill ["slot"]
        (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
        (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
          [0, 32]).1)⟦"offset" ↦ 0⟧.evm
      = (Clear.KeccakDeterminism.keccakOut
          (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32).2 := by
  have hmok : isOk (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hok
  simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil, evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.evm_setEvm_of_isOk hok]

/-- **STORAGE FRAME.**  The index-zero accessor writes no storage, on either branch. -/
lemma storage_array_index_access_bytes32_dyn_ptr_5303_sload
    {slot offset : Identifier} {array : Literal} {q : UInt256} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["array"],[array]⟧) := isOk_initcall_of_isOk hok
  have hgok : isOk ((s₀☎️⟦["array"],[array]⟧)⟦"split_expr_0" ↦
      Clear.EVMState.sload (s₀☎️⟦["array"],[array]⟧).evm
        ((s₀☎️⟦["array"],[array]⟧)["array"]!!)⟧) := isOk_insert.mpr hf0
  have hge : ((s₀☎️⟦["array"],[array]⟧)⟦"split_expr_0" ↦
      Clear.EVMState.sload (s₀☎️⟦["array"],[array]⟧).evm
        ((s₀☎️⟦["array"],[array]⟧)["array"]!!)⟧).evm = s₀.evm := by
    simp only [evm_insert]
    exact Clear.evm_initcall hok
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      Clear.KeccakPrimOps.primCall_keccakOut, isOutOfFuel_multifill', isOutOfFuel_setEvm']
    exact hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_6945705467323769142_isOk hgok hssnf hga
  have hse : Clear.EVMState.sload ss.evm q = Clear.EVMState.sload s₀.evm q := by
    rw [L2InteropCommitmentTree.Common.if_6945705467323769142_sload hgok hssnf hga, hge]
  have hrok : isOk ((Clear.State.multifill ["slot"]
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
        [0, 32]).1)⟦"offset" ↦ 0⟧) := by
    simp only [isOk_insert, Clear.KeccakPrimOps.primCall_keccakOut]
    exact isOk_multifill (by simp only [isOk_setEvm]; exact hssok)
  subst heq
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hrok, resultOf_evm hssok,
    Clear.StorageFrame.sload_keccakOut, Clear.StorageFrame.sload_mstore, hse]

/-- The guard's post-state, named once so the three lemmas below share a parse. -/
private def gState (array : Literal) (s₀ : State) : State :=
  let f := s₀☎️⟦["array"],[array]⟧
  f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧

private lemma gState_isOk {array : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (gState array s₀) := isOk_insert.mpr (isOk_initcall_of_isOk hok)

private lemma gState_evm {array : Literal} {s₀ : State} (hok : isOk s₀) :
    (gState array s₀).evm = s₀.evm := by
  simp only [gState, evm_insert]; exact Clear.evm_initcall hok

/-- **KECCAK WINDOW.**  One `mstore` below the window and one hash: both preserved. -/
lemma storage_array_index_access_bytes32_dyn_ptr_5303_config
    {slot offset : Identifier} {array : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := gState_isOk (array := array) hok
  have hge := gState_evm (array := array) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      Clear.KeccakPrimOps.primCall_keccakOut, isOutOfFuel_multifill', isOutOfFuel_setEvm']
    exact hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_6945705467323769142_isOk hgok hssnf hga
  obtain ⟨hRss, hCss⟩ := L2InteropCommitmentTree.Common.if_6945705467323769142_config hgok hssnf
    (by rw [hge]; exact hR) (by rw [hge]; exact hC) hga
  have hrok : isOk ((Clear.State.multifill ["slot"]
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
        [0, 32]).1)⟦"offset" ↦ 0⟧) := by
    simp only [isOk_insert, Clear.KeccakPrimOps.primCall_keccakOut]
    exact isOk_multifill (by simp only [isOk_setEvm]; exact hssok)
  subst heq
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hrok, resultOf_evm hssok]
  have hRm := Clear.StorageFrame.rangeInWindow_mstore (a := 0) (v := ss["array"]!!) hRss
  have hCm := Clear.StorageFrame.cachedInWindow_mstore (a := 0) (v := ss["array"]!!) hCss
  exact ⟨Clear.KeccakLowSlot.rangeInWindow_keccakOut hRm,
    Clear.KeccakLowSlot.cachedInWindow_keccakOut hRm hCm⟩

/-- **FUEL.**  One hash: the accessor costs exactly one unit, on either branch of the guard. -/
lemma storage_array_index_access_bytes32_dyn_ptr_5303_fuel
    {slot offset : Identifier} {array : Literal} {k : ℕ} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm (k + 1))
    (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) :
    Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := gState_isOk (array := array) hok
  have hge := gState_evm (array := array) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      Clear.KeccakPrimOps.primCall_keccakOut, isOutOfFuel_multifill', isOutOfFuel_setEvm']
    exact hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_6945705467323769142_isOk hgok hssnf hga
  have hfss : Clear.KeccakFuel.Fuel ss.evm (k + 1) :=
    L2InteropCommitmentTree.Common.if_6945705467323769142_fuel hgok hssnf
      (by rw [hge]; exact hf) hga
  have hrok : isOk ((Clear.State.multifill ["slot"]
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
        [0, 32]).1)⟦"offset" ↦ 0⟧) := by
    simp only [isOk_insert, Clear.KeccakPrimOps.primCall_keccakOut]
    exact isOk_multifill (by simp only [isOk_setEvm]; exact hssok)
  subst heq
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hrok, resultOf_evm hssok]
  exact Clear.KeccakFuel.Fuel.keccakOut (Clear.KeccakFuel.Fuel.mstore 0 _ hfss)

/-- The returned slot, on EITHER branch of the guard: the hash itself, no offset. -/
private lemma slot_resultOf {ss : State} (hok : isOk ss) :
    (Clear.State.multifill ["slot"]
        (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
        (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
          [0, 32]).1)⟦"offset" ↦ 0⟧["slot"]!!
      = (Clear.KeccakDeterminism.keccakOut
          (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32).1 := by
  have hmok : isOk (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hok
  simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil]
  rw [lookup_insert_of_ne (by decide),
    lookup_insert' (by simp only [isOk_setEvm]; exact hok), Clear.evm_setEvm_of_isOk hok]

private lemma zero_lt_lowSlotBound :
    (0 : UInt256).val < Clear.KeccakInjective.lowSlotBound := by
  show (0 : ℕ) < 2 ^ 32
  norm_num

/-- **THE ELEMENT-0 SLOT IS NEVER A LOW SLOT.**

The index-zero variant returns `keccak(array)` with no `+ index`, so unlike its indexed
sibling this owes nothing about an index bound -- the caller supplies only the keccak
configuration and one unit of fuel.  As there, it holds on BOTH branches of the empty-array
guard: the address computation runs either way, because a revert is a flag rather than a
rollback in this model. -/
lemma storage_array_index_access_bytes32_dyn_ptr_5303_slot_not_low
    {slot offset : Identifier} {array c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 1)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_storage_array_index_access_bytes32_dyn_ptr_5303 slot offset array s₀ s₉) :
    s₉[slot]!! ≠ c := by
  obtain ⟨ss, hg, heq⟩ := h
  have hgok := gState_isOk (array := array) hok
  have hge := gState_evm (array := array) hok
  have hssnf : ¬ ❓ ss := by
    intro hoo; apply hnf; rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      Clear.KeccakPrimOps.primCall_keccakOut, isOutOfFuel_multifill', isOutOfFuel_setEvm']
    exact hoo
  have hga := Spec_ok_unfold hgok hssnf hg
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_6945705467323769142_isOk hgok hssnf hga
  obtain ⟨hRss, hCss⟩ := L2InteropCommitmentTree.Common.if_6945705467323769142_config hgok hssnf
    (by rw [hge]; exact hR) (by rw [hge]; exact hC) hga
  have hfss : Clear.KeccakFuel.Fuel ss.evm 1 :=
    L2InteropCommitmentTree.Common.if_6945705467323769142_fuel hgok hssnf
      (by rw [hge]; exact hf) hga
  have hrok : isOk ((Clear.State.multifill ["slot"]
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
        [0, 32]).1)⟦"offset" ↦ 0⟧) := by
    simp only [isOk_insert, Clear.KeccakPrimOps.primCall_keccakOut]
    exact isOk_multifill (by simp only [isOk_setEvm]; exact hssok)
  have hrev : isOk (🧟 ((Clear.State.multifill ["slot"]
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256 [0, 32]).2
      (primCall (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) .Keccak256
        [0, 32]).1)⟦"offset" ↦ 0⟧)) := by
    rw [revive_of_ok hrok]; exact hrok
  subst heq
  rw [lookup_insert' (isOk_insert.mpr (isOk_setStore_of_isOk hrev)), slot_resultOf hssok]
  have hRm := Clear.StorageFrame.rangeInWindow_mstore (a := 0) (v := ss["array"]!!) hRss
  have hCm := Clear.StorageFrame.cachedInWindow_mstore (a := 0) (v := ss["array"]!!) hCss
  obtain ⟨r, σ', hsome⟩ := Clear.KeccakFuel.keccak256_some_of_fuel (p := 0) (q := 32)
    (Clear.KeccakFuel.Fuel.mstore 0 (ss["array"]!!) hfss)
  have hko : Clear.KeccakDeterminism.keccakOut
      (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32 = (r, σ') := by
    unfold Clear.KeccakDeterminism.keccakOut; rw [hsome]
  rw [hko]
  -- the `+ 0` route: the window predicates are the ones the config frames carry, and the
  -- indexed lemma specialises to no offset
  have := Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config (j := 0) c hRm hCm hsome
    zero_lt_lowSlotBound hcl
  simpa using this

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
