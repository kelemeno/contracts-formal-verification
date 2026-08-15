import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakFresh
import specs.KeccakSlotSep
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.KeccakFuel
import specs.KeccakInjective
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

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

/-- **Where the element is.**  When the bounds check passes, the returned slot is
`keccak(array) + index` — over the caller's own arguments and `s₀.evm`.

This is the equation the fold bridge needs: it turns "the accessor was called" into "the
element was read from THIS slot", so a fold step can be stated in terms of the tree's
contents rather than an intermediate state.

Proof note: every `isOk` side condition is `have`d with its type written out and passed by
NAME.  Passing one as `(by …)` inside `rw [...]` leaves the lemma instance undetermined and
the rewrite fails with "pattern not found" and metavariables in the pattern -- which reads
like a shape mismatch and is not one. -/
lemma storage_array_index_access_bytes32_dyn_ptr_val
    {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hso : slot ≠ offset)
    (hlt : index < Clear.EVMState.sload s₀.evm array)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[slot]!! = (keccakOut ((s₀.evm).mstore 0 array) 0 32).1 + index := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! ≠ 0 := by
    rw [arrIdxGuardState_flag hok]; simp [hlt]
  have hss : ss = arrIdxGuardState array index s₀ :=
    (Spec_ok_unfold hgcok hssnf hg).1 hflag
  subst hss
  subst heq
  have hgcnf : ¬ ❓ (arrIdxGuardState array index s₀) := fun hoo =>
    isOk_and_isOutOfFuel ⟨hgcok, hoo⟩
  have hrev : isOk (🧟(arrIdxResultState (arrIdxGuardState array index s₀))) :=
    Clear.isOk_reviveJump_of_not_isOutOfFuel (by
      rw [isOutOfFuel_arrIdxResultState]; exact hgcnf)
  rw [lookup_insert' (isOk_insert.mpr (isOk_setStore_of_isOk hrev))]
  unfold arrIdxResultState
  set M := (arrIdxGuardState array index s₀)🇪⟦Clear.EVMState.mstore
    (arrIdxGuardState array index s₀).evm 0
    ((arrIdxGuardState array index s₀)["array"]!!)⟧ with hM
  have hmok : isOk M := by rw [hM]; simp only [isOk_setEvm]; exact hgcok
  have hkk : isOk (Clear.State.multifill ["split_expr_2"]
      (primCall M .Keccak256 [0, 32]).2 (primCall M .Keccak256 [0, 32]).1) := by
    simp only [primCall_keccakOut]
    exact isOk_multifill (by simp only [isOk_setEvm]; exact hmok)
  have houter : isOk (M🇪⟦(keccakOut M.evm 0 32).2⟧) := by
    simp only [isOk_setEvm]; exact hmok
  rw [lookup_insert_of_ne (by decide), lookup_insert' hkk]
  simp only [primCall_keccakOut, multifill_cons, multifill_nil]
  rw [lookup_insert' houter]
  -- goal: (keccakOut M.evm 0 32).1 + (M🇪⟦…⟧⟦"split_expr_2"↦…⟧["index"]!!) = …
  -- skip the split_expr_2 insert, then peel the setEvm, then unfold M
  rw [lookup_insert_of_ne (by decide), Clear.lookup_setEvm hmok, hM,
    Clear.lookup_setEvm hgcok, arrIdxGuardState_index hok,
    Clear.evm_setEvm_of_isOk hgcok, arrIdxGuardState_array hok, arrIdxGuardState_evm hok]


/-- **FRAME.**  The accessor writes only `slot` and `offset`; everything else is the
caller's.  Note this needs NO bounds hypothesis -- an out-of-range call reverts, and a
reverting call is not `Ok`, so `hnf` already covers it. -/
lemma storage_array_index_access_bytes32_dyn_ptr_frame
    {slot offset : Identifier} {array index : Literal} {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hvs : v ≠ slot) (hvo : v ≠ offset)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 (arrIdxResultState ss)) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hvs, lookup_insert_of_ne hvo, Clear.lookup_setStore hrev hok]


/-- The result state's evm chain -- `mstore`, hash, then inserts -- writes no storage. -/
private lemma sload_arrIdxResultState {ss : State} {q : Literal} (hok : isOk ss) :
    Clear.EVMState.sload (arrIdxResultState ss).evm q = Clear.EVMState.sload ss.evm q := by
  unfold arrIdxResultState
  set M := ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧ with hM
  have hmok : isOk M := by rw [hM]; simp only [isOk_setEvm]; exact hok
  simp only [primCall_keccakOut, multifill_cons, multifill_nil, evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.StorageFrame.sload_keccakOut, hM,
    Clear.evm_setEvm_of_isOk hok, Clear.StorageFrame.sload_mstore]

/-- **STORAGE FRAME.**  The accessor computes an address: it `mstore`s the array slot and
hashes it, and writes NO storage.  So every slot reads back the same across the call.

UNCONDITIONAL -- unlike `_val`, this needs no bounds hypothesis.  Out of bounds the code
panics, and a panic does not write storage either
(`Clear.StorageFrame.sload_evm_revert`), so both branches preserve every slot.  That
matters for a caller: `isOk s₉` does NOT rule out the panic branch, since Clear models a
revert as a flag on an otherwise-`Ok` state. -/
lemma storage_array_index_access_bytes32_dyn_ptr_sload
    {slot offset : Identifier} {array index q : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hga := Spec_ok_unfold hgcok hssnf hg
  -- both branches: `ss` is `Ok`, and reads the same storage as the guard state
  have hboth : isOk ss ∧ Clear.EVMState.sload ss.evm q
      = Clear.EVMState.sload (arrIdxGuardState array index s₀).evm q := by
    by_cases hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! = 0
    · obtain ⟨sp, hsp, hss⟩ := hga.2 hflag
      subst hss
      exact ⟨panic_error_0x32_isOk hgcok (Spec_ok_unfold hgcok hssnf hsp),
        panic_error_0x32_sload hgcok (Spec_ok_unfold hgcok hssnf hsp)⟩
    · have hss : ss = arrIdxGuardState array index s₀ := hga.1 hflag
      subst hss
      exact ⟨hgcok, rfl⟩
  subst heq
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk (isOk_arrIdxResultState hboth.1),
    sload_arrIdxResultState hboth.1, hboth.2, arrIdxGuardState_evm hok]


/-- **CONFIG FRAME.**  The accessor's `mstore` + hash leave the keccak window intact, on
BOTH branches -- the bounds panic reverts, which does not touch it either. -/
lemma storage_array_index_access_bytes32_dyn_ptr_config
    {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hgce : (arrIdxGuardState array index s₀).evm = s₀.evm := arrIdxGuardState_evm hok
  have hga := Spec_ok_unfold hgcok hssnf hg
  -- both branches keep the window
  have hboth : isOk ss ∧ RangeInWindow ss.evm ∧ CachedInWindow ss.evm := by
    by_cases hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! = 0
    · obtain ⟨sp, hsp, hss⟩ := hga.2 hflag
      subst hss
      refine ⟨panic_error_0x32_isOk hgcok (Spec_ok_unfold hgcok hssnf hsp), ?_⟩
      exact panic_error_0x32_config hgcok (by rw [hgce]; exact hR) (by rw [hgce]; exact hC)
        (Spec_ok_unfold hgcok hssnf hsp)
    · have hss : ss = arrIdxGuardState array index s₀ := hga.1 hflag
      subst hss
      exact ⟨hgcok, by rw [hgce]; exact hR, by rw [hgce]; exact hC⟩
  obtain ⟨hssok, hRss, hCss⟩ := hboth
  subst heq
  have hrsok : isOk (arrIdxResultState ss) := isOk_arrIdxResultState hssok
  have hev : ((🧟 (arrIdxResultState ss))🏪⟦s₀⟧⟦offset ↦ (arrIdxResultState ss)["offset"]!!⟧⟦slot
      ↦ (arrIdxResultState ss)["slot"]!!⟧).evm
      = (keccakOut (EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32).2 := by
    simp only [evm_insert, evm_setStore]
    rw [Clear.evm_reviveJump_of_isOk hrsok]
    unfold arrIdxResultState
    have hmok : isOk (ss🇪⟦EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) := by
      simp only [isOk_setEvm]; exact hssok
    simp only [primCall_keccakOut, multifill_cons, multifill_nil, evm_insert]
    rw [Clear.evm_setEvm_of_isOk hmok, Clear.evm_setEvm_of_isOk hssok]
  rw [hev]
  have hRm : RangeInWindow (EVMState.mstore ss.evm 0 (ss["array"]!!)) := rangeInWindow_mstore hRss
  have hCm : CachedInWindow (EVMState.mstore ss.evm 0 (ss["array"]!!)) := cachedInWindow_mstore hCss
  exact ⟨rangeInWindow_keccakOut hRm, cachedInWindow_keccakOut hRm hCm⟩


/-- **THE ACCESSOR NEVER RETURNS A LOW SLOT.**

`_val` says the slot is `keccak(array) + index`; `KeccakLowSlot` says a freshly minted
keccak value plus a small offset is never a low slot.  Joining them is what turns "the
fold writes SOME slot" into "the fold does not write slot `c`" -- and `c` is what a caller
can name: the level count lives at a literal low slot.

The side conditions are real and belong to the caller, not to this lemma:
  * `hR`/`hC`  the keccak window, which the config frames carry to here;
  * `hclean`   the hash step did not exhaust the pool (no collision flag);
  * `hj`       the index is below `2 ^ 32` -- true of any real tree, not provable here;
  * `hc`       the target slot is below `2 ^ 32`, which a literal slot number is. -/
lemma storage_array_index_access_bytes32_dyn_ptr_slot_ne_low
    {slot offset : Identifier} {array index c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hso : slot ≠ offset)
    (hlt : index < Clear.EVMState.sload s₀.evm array)
    (hR : RangeInWindow ((s₀.evm).mstore 0 array))
    (hC : CachedInWindow ((s₀.evm).mstore 0 array))
    (hclean : (keccakOut ((s₀.evm).mstore 0 array) 0 32).2.hash_collision = false)
    (hj : index.val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[slot]!! ≠ c := by
  rw [storage_array_index_access_bytes32_dyn_ptr_val hok hnf hso hlt h]
  exact Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config index c hR hC
    (Clear.KeccakDeterminism.keccakOut_some_of_clean hclean) hj hcl


/-- **THE ACCESSOR'S SLOT MISSES ANY OTHER CACHED-PLUS-OFFSET SLOT.**

The low-slot companion rules out collisions with LITERAL slots.  This rules out collisions
with the other keccak-derived family: a level array's LENGTH slot is `keccak(nodes) + i`,
which is not a low slot at all, so `_slot_ne_low` says nothing about it.  That is an
offset-vs-offset question and `KeccakSlotSep.cached_off_ne_off` is its answer.

The two hashes must be CACHED in the same state, which is how the fold actually runs: the
level array's slot is computed by an earlier accessor call in the same body, so by the time
the node slot is hashed both intervals are in the cache.  `mkInterval_0_32_ne_of_word0_ne`
supplies the `hne` at the use site, from the two arrays being different words.

Axiom-free: `cached_off_ne_off` rests on the cache CONFIGURATION, not on keccak
injectivity. -/
lemma storage_array_index_access_bytes32_dyn_ptr_slot_ne_cached
    {slot offset : Identifier} {array index r₁ r₂ k₂ : Literal} {I₂ : List UInt256}
    {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hso : slot ≠ offset)
    (hlt : index < Clear.EVMState.sload s₀.evm array)
    (hsep : Clear.KeccakSlotSep.Separated ((s₀.evm).mstore 0 array))
    (hinj : Clear.KeccakFresh.CacheInj ((s₀.evm).mstore 0 array))
    (hc₁ : Finmap.lookup (EVMState.mkInterval ((s₀.evm).mstore 0 array).machine_state 0 32)
             ((s₀.evm).mstore 0 array).keccak_map = some r₁)
    (hc₂ : Finmap.lookup I₂ ((s₀.evm).mstore 0 array).keccak_map = some r₂)
    (hne : EVMState.mkInterval ((s₀.evm).mstore 0 array).machine_state 0 32 ≠ I₂)
    (hk₁ : index.val < Clear.KeccakInjective.lowSlotBound)
    (hk₂ : k₂.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[slot]!! ≠ r₂ + k₂ := by
  rw [storage_array_index_access_bytes32_dyn_ptr_val hok hnf hso hlt h,
    Clear.KeccakDeterminism.keccakOut_of_cached hc₁]
  exact Clear.KeccakSlotSep.cached_off_ne_off hsep hinj hc₁ hc₂ hne hk₁ hk₂


/-- **THE FRESH-MINT FORM.**  Same conclusion as `_slot_ne_cached`, but stated where the
fold can actually discharge it.

The accessor's own hash may be a MINT (the first time that level array is hashed in this
call), so its value is not in the cache BEFORE the call and the cached form does not apply.
It is in the cache AFTER (`keccakOut_caches_of_clean`), and the other value is still there
because the cache only grows -- so both are cached at the POST-hash state, and the
inequality `cached_off_ne_off` proves there is an inequality between two `UInt256`s, which
holds everywhere.

That is the whole trick: state the hypotheses at the post-hash state and the fresh/cached
asymmetry disappears. -/
lemma storage_array_index_access_bytes32_dyn_ptr_slot_ne_post
    {slot offset : Identifier} {array index r₂ k₂ : Literal} {I₂ : List UInt256}
    {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hso : slot ≠ offset)
    (hlt : index < Clear.EVMState.sload s₀.evm array)
    (hclean : (keccakOut ((s₀.evm).mstore 0 array) 0 32).2.hash_collision = false)
    (hsep : Clear.KeccakSlotSep.Separated (keccakOut ((s₀.evm).mstore 0 array) 0 32).2)
    (hinj : Clear.KeccakFresh.CacheInj (keccakOut ((s₀.evm).mstore 0 array) 0 32).2)
    (hc₂ : Finmap.lookup I₂ (keccakOut ((s₀.evm).mstore 0 array) 0 32).2.keccak_map
             = some r₂)
    (hne : EVMState.mkInterval ((s₀.evm).mstore 0 array).machine_state 0 32 ≠ I₂)
    (hk₁ : index.val < Clear.KeccakInjective.lowSlotBound)
    (hk₂ : k₂.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[slot]!! ≠ r₂ + k₂ := by
  have hc₁ := Clear.KeccakDeterminism.keccakOut_caches_of_clean hclean
  rw [storage_array_index_access_bytes32_dyn_ptr_val hok hnf hso hlt h]
  exact Clear.KeccakSlotSep.cached_off_ne_off hsep hinj hc₁ hc₂ hne hk₁ hk₂

/-- The offset output is `0` on BOTH branches -- it is a literal in the code, not something
computed from the index -- so unlike `_val` this needs no bounds hypothesis. -/
lemma arrIdxResultState_offset {ss : State} (h : isOk ss) :
    (arrIdxResultState ss)["offset"]!! = 0 := by
  unfold arrIdxResultState
  refine lookup_insert' ?_
  simp only [isOk_insert, primCall_keccakOut]
  exact isOk_multifill (by simpa [isOk_setEvm] using h)

/-- **THE ELEMENT IS WORD-ALIGNED.**  `offset = 0`: a `bytes32` fills its slot, so the
writer's mask collapses and the element is stored outright.  This is what connects the
accessor to `update_storage_value_bytes32_to_bytes32_val`. -/
lemma storage_array_index_access_bytes32_dyn_ptr_offset
    {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hso : slot ≠ offset)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[offset]!! = 0 := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hssok : isOk ss :=
    L2InteropCommitmentTree.Common.if_2600721580863995212_isOk hgcok hssnf
      (Spec_ok_unfold hgcok hssnf hg)
  have hrok : isOk (arrIdxResultState ss) := isOk_arrIdxResultState hssok
  have hrev : isOk (🧟(arrIdxResultState ss)) := by rw [revive_of_ok hrok]; exact hrok
  subst heq
  rw [lookup_insert_of_ne (Ne.symm hso), lookup_insert' (isOk_setStore_of_isOk hrev)]
  exact arrIdxResultState_offset hssok

private lemma account_arrIdxResultState {ss : State} {addr : Address} (hok : isOk ss) :
    Clear.EVMState.lookupAccount (arrIdxResultState ss).evm addr
        = Clear.EVMState.lookupAccount ss.evm addr ∧
      (arrIdxResultState ss).evm.execution_env = ss.evm.execution_env := by
  unfold arrIdxResultState
  set M := ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧ with hM
  have hmok : isOk M := by rw [hM]; simp only [isOk_setEvm]; exact hok
  simp only [primCall_keccakOut, multifill_cons, multifill_nil, evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.StorageFrame.lookupAccount_keccakOut,
    Clear.StorageFrame.execution_env_keccakOut, hM, Clear.evm_setEvm_of_isOk hok,
    Clear.StorageFrame.lookupAccount_mstore, Clear.StorageFrame.execution_env_mstore]
  exact ⟨rfl, rfl⟩

/-- **ACCOUNT FRAME.**  The accessor computes an address: it `mstore`s and hashes, and on
the out-of-bounds path it panics and reverts.  None of that removes the contract's account
or changes which address is `code_owner`.

UNCONDITIONAL, like `_sload`, and for the same reason: a revert is a flag in this model,
so both branches preserve the account.  This is what carries `sload_sstore_self`'s
hypothesis from before the accessor call to after it. -/
lemma storage_array_index_access_bytes32_dyn_ptr_account
    {slot offset : Identifier} {array index : Literal} {addr : Address} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    Clear.EVMState.lookupAccount s₉.evm addr = Clear.EVMState.lookupAccount s₀.evm addr ∧
      s₉.evm.execution_env = s₀.evm.execution_env := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hga := Spec_ok_unfold hgcok hssnf hg
  have hboth : isOk ss ∧
      (Clear.EVMState.lookupAccount ss.evm addr
          = Clear.EVMState.lookupAccount (arrIdxGuardState array index s₀).evm addr ∧
        ss.evm.execution_env = (arrIdxGuardState array index s₀).evm.execution_env) := by
    by_cases hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! = 0
    · obtain ⟨sp, hsp, hss⟩ := hga.2 hflag
      subst hss
      exact ⟨panic_error_0x32_isOk hgcok (Spec_ok_unfold hgcok hssnf hsp),
        panic_error_0x32_account hgcok (Spec_ok_unfold hgcok hssnf hsp)⟩
    · have hss : ss = arrIdxGuardState array index s₀ := hga.1 hflag
      subst hss
      exact ⟨hgcok, rfl, rfl⟩
  subst heq
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk (isOk_arrIdxResultState hboth.1)]
  obtain ⟨hacc', henv'⟩ := (account_arrIdxResultState (addr := addr) hboth.1)
  rw [hacc', henv', hboth.2.1, hboth.2.2, arrIdxGuardState_evm hok]
  exact ⟨rfl, rfl⟩

/-- **FUEL FRAME.**  The accessor hashes once, so it costs at most one unit of pool; the
out-of-bounds branch panics, which costs nothing.  Unconditional, like `_sload` and
`_config`, and for the same reason -- a revert is a flag here, not a rollback.

This is what lets a caller's hash budget reach a LATER hash on the same path.  Without it
the low-slot separations stop being dischargeable after the first accessor call. -/
lemma storage_array_index_access_bytes32_dyn_ptr_fuel
    {slot offset : Identifier} {array index : Literal} {k : ℕ} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hf : Clear.KeccakFuel.Fuel s₀.evm (k + 1))
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf0
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hgce : (arrIdxGuardState array index s₀).evm = s₀.evm := arrIdxGuardState_evm hok
  have hga := Spec_ok_unfold hgcok hssnf hg
  -- both branches leave at least `k + 1` units: the panic spends nothing, the identity
  -- branch is the caller's own state
  have hboth : isOk ss ∧ Clear.KeccakFuel.Fuel ss.evm (k + 1) := by
    by_cases hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! = 0
    · obtain ⟨sp, hsp, hss⟩ := hga.2 hflag
      subst hss
      exact ⟨panic_error_0x32_isOk hgcok (Spec_ok_unfold hgcok hssnf hsp),
        panic_error_0x32_fuel hgcok (by rw [hgce]; exact hf)
          (Spec_ok_unfold hgcok hssnf hsp)⟩
    · have hss : ss = arrIdxGuardState array index s₀ := hga.1 hflag
      subst hss
      exact ⟨hgcok, by rw [hgce]; exact hf⟩
  obtain ⟨hssok, hfss⟩ := hboth
  subst heq
  have hrsok : isOk (arrIdxResultState ss) := isOk_arrIdxResultState hssok
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hrsok]
  unfold arrIdxResultState
  have hmok : isOk (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hssok
  simp only [primCall_keccakOut, multifill_cons, multifill_nil, evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.evm_setEvm_of_isOk hssok]
  exact Clear.KeccakFuel.Fuel.keccakOut (Clear.KeccakFuel.Fuel.mstore 0 _ hfss)

/-- The result state's slot, in terms of the state the guard produced -- on EITHER branch. -/
private lemma slot_arrIdxResultState {ss : State} (hok : isOk ss) :
    (arrIdxResultState ss)["slot"]!!
      = (Clear.KeccakDeterminism.keccakOut
          (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32).1 + (ss["index"]!!) := by
  unfold arrIdxResultState
  have hmok : isOk (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hok
  simp only [primCall_keccakOut, multifill_cons, multifill_nil]
  rw [lookup_insert_of_ne (by decide), lookup_insert' (isOk_insert.mpr
      (by simp only [isOk_setEvm]; exact hok)),
    lookup_insert' (by simp only [isOk_setEvm]; exact hok),
    lookup_insert_of_ne (by decide), Clear.lookup_setEvm hmok, Clear.lookup_setEvm hok,
    Clear.evm_setEvm_of_isOk hok]

/-- **THE ELEMENT SLOT IS NEVER A LOW SLOT -- AND THIS DOES NOT NEED THE BOUNDS CHECK.**

`_val` and `_slot_ne_low` both require `hlt`, and inside the fold that hypothesis IS the
still-open `maxNodeNumber < _nodes[i].length` invariant.  They need it because they say WHICH
slot, in closed form over `s₀.evm`, and the panic branch changes the evm.

This says only that the slot is not one of the tree's constant-numbered ones, and that holds
on BOTH branches: the guard decides whether to panic, but the address computation -- `mstore`,
hash, `slot`/`offset` -- runs either way, because a revert is a flag in this model rather
than a rollback.  So a caller framing a literal slot past an accessor call owes the keccak
configuration and nothing about the array's length. -/
lemma storage_array_index_access_bytes32_dyn_ptr_slot_not_low
    {slot offset : Identifier} {array index c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 1)
    (hj : index.val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[slot]!! ≠ c := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf0
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hgce : (arrIdxGuardState array index s₀).evm = s₀.evm := arrIdxGuardState_evm hok
  have hgci : (arrIdxGuardState array index s₀)["index"]!! = index :=
    arrIdxGuardState_index hok
  have hga := Spec_ok_unfold hgcok hssnf hg
  -- both branches: `Ok`, same window, same fuel, same `index`
  have hboth : isOk ss ∧ (Clear.KeccakLowSlot.RangeInWindow ss.evm ∧
      Clear.KeccakLowSlot.CachedInWindow ss.evm) ∧
      Clear.KeccakFuel.Fuel ss.evm 1 ∧ ss["index"]!! = index := by
    by_cases hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! = 0
    · obtain ⟨sp, hsp, hss⟩ := hga.2 hflag
      subst hss
      have hspa := Spec_ok_unfold hgcok hssnf hsp
      refine ⟨panic_error_0x32_isOk hgcok hspa, ?_, ?_, ?_⟩
      · exact panic_error_0x32_config hgcok (by rw [hgce]; exact hR) (by rw [hgce]; exact hC) hspa
      · exact panic_error_0x32_fuel hgcok (by rw [hgce]; exact hf) hspa
      · rw [panic_error_0x32_frame hgcok hspa]; exact hgci
    · have hss : ss = arrIdxGuardState array index s₀ := hga.1 hflag
      subst hss
      exact ⟨hgcok, ⟨by rw [hgce]; exact hR, by rw [hgce]; exact hC⟩,
        by rw [hgce]; exact hf, hgci⟩
  obtain ⟨hssok, ⟨hRss, hCss⟩, hfss, hidx⟩ := hboth
  have hrsok : isOk (arrIdxResultState ss) := isOk_arrIdxResultState hssok
  have hrev : isOk (🧟(arrIdxResultState ss)) := by
    rw [revive_of_ok hrsok]; exact hrsok
  subst heq
  rw [lookup_insert' (isOk_insert.mpr (isOk_setStore_of_isOk hrev)),
    slot_arrIdxResultState hssok, hidx]
  -- the hash at the state the address computation actually runs from
  have hRm := Clear.StorageFrame.rangeInWindow_mstore (a := 0) (v := ss["array"]!!) hRss
  have hCm := Clear.StorageFrame.cachedInWindow_mstore (a := 0) (v := ss["array"]!!) hCss
  obtain ⟨r, σ', hsome⟩ := Clear.KeccakFuel.keccak256_some_of_fuel (p := 0) (q := 32)
    (Clear.KeccakFuel.Fuel.mstore 0 (ss["array"]!!) hfss)
  have hko : Clear.KeccakDeterminism.keccakOut
      (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32 = (r, σ') := by
    unfold Clear.KeccakDeterminism.keccakOut
    rw [hsome]
  rw [hko]
  exact Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config _ _ hRm hCm hsome hj hcl

/-- The result state's evm IS the hash's post-state, on either branch of the guard. -/
private lemma evm_arrIdxResultState {ss : State} (hok : isOk ss) :
    (arrIdxResultState ss).evm
      = (Clear.KeccakDeterminism.keccakOut
          (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32).2 := by
  unfold arrIdxResultState
  have hmok : isOk (ss🇪⟦Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hok
  simp only [primCall_keccakOut, multifill_cons, multifill_nil, evm_insert]
  rw [Clear.evm_setEvm_of_isOk hmok, Clear.evm_setEvm_of_isOk hok]

/-- **THE SAME RESULT, PAID FOR BY THE CLEAN FLAG RATHER THAN BY FUEL.**

The indexed sibling of `..._5303_slot_not_low_of_clean`, and the one the fold body needs:
an exhausted keccak pool raises `hash_collision` instead of leaving the `Ok` world, so a
clear flag on the state in hand witnesses that the hash genuinely succeeded.

The index bound `hj` stays -- unlike the clean flag it is not about whether the hash ran,
but about the `+ index` that follows it, which could in principle wrap a fresh high hash
back down onto a constant-numbered slot. -/
lemma storage_array_index_access_bytes32_dyn_ptr_slot_not_low_of_clean
    {slot offset : Identifier} {array index c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : s₉.evm.hash_collision = false)
    (hj : index.val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : A_storage_array_index_access_bytes32_dyn_ptr slot offset array index s₀ s₉) :
    s₉[slot]!! ≠ c := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf0 : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardState array index s₀) := by
    unfold arrIdxGuardState; simpa [isOk_insert] using hf0
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultState]
    exact hoo
  have hgce : (arrIdxGuardState array index s₀).evm = s₀.evm := arrIdxGuardState_evm hok
  have hgci : (arrIdxGuardState array index s₀)["index"]!! = index :=
    arrIdxGuardState_index hok
  have hga := Spec_ok_unfold hgcok hssnf hg
  -- both branches: `Ok`, same window, same `index` -- no fuel needed now
  have hboth : isOk ss ∧ (Clear.KeccakLowSlot.RangeInWindow ss.evm ∧
      Clear.KeccakLowSlot.CachedInWindow ss.evm) ∧ ss["index"]!! = index := by
    by_cases hflag : (arrIdxGuardState array index s₀)["split_expr_1"]!! = 0
    · obtain ⟨sp, hsp, hss⟩ := hga.2 hflag
      subst hss
      have hspa := Spec_ok_unfold hgcok hssnf hsp
      refine ⟨panic_error_0x32_isOk hgcok hspa, ?_, ?_⟩
      · exact panic_error_0x32_config hgcok (by rw [hgce]; exact hR) (by rw [hgce]; exact hC) hspa
      · rw [panic_error_0x32_frame hgcok hspa]; exact hgci
    · have hss : ss = arrIdxGuardState array index s₀ := hga.1 hflag
      subst hss
      exact ⟨hgcok, ⟨by rw [hgce]; exact hR, by rw [hgce]; exact hC⟩, hgci⟩
  obtain ⟨hssok, ⟨hRss, hCss⟩, hidx⟩ := hboth
  have hrsok : isOk (arrIdxResultState ss) := isOk_arrIdxResultState hssok
  have hrev : isOk (🧟(arrIdxResultState ss)) := by
    rw [revive_of_ok hrsok]; exact hrsok
  -- the caller's clear flag is the hash's own post-state flag
  have hcl2 : (Clear.KeccakDeterminism.keccakOut
      (Clear.EVMState.mstore ss.evm 0 (ss["array"]!!)) 0 32).2.hash_collision = false := by
    rw [heq] at hclean
    simpa only [evm_insert, evm_setStore, Clear.evm_reviveJump_of_isOk hrsok,
      evm_arrIdxResultState hssok] using hclean
  have hsome := Clear.KeccakDeterminism.keccakOut_some_of_clean hcl2
  subst heq
  rw [lookup_insert' (isOk_insert.mpr (isOk_setStore_of_isOk hrev)),
    slot_arrIdxResultState hssok, hidx]
  have hRm := Clear.StorageFrame.rangeInWindow_mstore (a := 0) (v := ss["array"]!!) hRss
  have hCm := Clear.StorageFrame.cachedInWindow_mstore (a := 0) (v := ss["array"]!!) hCss
  exact Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config _ _ hRm hCm hsome hj hcl

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
