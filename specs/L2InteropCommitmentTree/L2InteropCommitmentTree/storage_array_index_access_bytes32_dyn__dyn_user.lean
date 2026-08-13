import Clear.ReasoningPrinciple
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- The state the bounds guard sees: parameters bound, length loaded, comparison made. -/
def arrIdxGuardStateDyn (array index : Literal) (s₀ : State) : State :=
  let f := s₀☎️⟦["array", "index"],[array, index]⟧
  let g := f⟦"split_expr_0" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  g⟦"split_expr_1" ↦ (decide (g["index"]!! < (g["split_expr_0"]!!))).toUInt256⟧

/-- The state after the element address is computed: `keccak(array) + index`, offset 0. -/
def arrIdxResultStateDyn (ss : State) : State :=
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
def A_storage_array_index_access_bytes32_dyn__dyn (slot offset : Identifier)
    (array index : Literal) (s₀ s₉ : State) : Prop :=
  ∃ ss, Spec L2InteropCommitmentTree.Common.A_if_2600721580863995212
      (arrIdxGuardStateDyn array index s₀) ss ∧
    s₉ = 🧟(arrIdxResultStateDyn ss)🏪⟦s₀⟧⟦offset ↦ (arrIdxResultStateDyn ss)["offset"]!!⟧⟦slot ↦
      (arrIdxResultStateDyn ss)["slot"]!!⟧

lemma storage_array_index_access_bytes32_dyn__dyn_abs_of_concrete {s₀ s₉ : State} {slot offset array index} :
  Spec (storage_array_index_access_bytes32_dyn__dyn_concrete_of_code.1 slot offset array index) s₀ s₉ →
  Spec (A_storage_array_index_access_bytes32_dyn__dyn slot offset array index) s₀ s₉ := by
  unfold storage_array_index_access_bytes32_dyn__dyn_concrete_of_code A_storage_array_index_access_bytes32_dyn__dyn
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hg, heq⟩ := hc
  exact ⟨ss, hg, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma storage_array_index_access_bytes32_dyn__dyn_isOk {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_storage_array_index_access_bytes32_dyn__dyn slot offset array index s₀ s₉) : isOk s₉ := by
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

lemma storage_array_index_access_bytes32_dyn__dyn_not_break {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_storage_array_index_access_bytes32_dyn__dyn slot offset array index s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (storage_array_index_access_bytes32_dyn__dyn_isOk hnf h)

/-- **`initcall` preserves the evm** for this call's parameter list. -/
lemma initcall_evm_ai_dyn {s : State} {a i : Literal} (h : isOk s) :
    (s☎️⟦["array", "index"],[a, i]⟧).evm = s.evm := by
  rcases s with ⟨evm, store⟩ | _ | _
  · simp only [State.initcall, multifill_cons, multifill_nil, evm_insert, evm_setStore]
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- **The bounds flag, in the caller's terms.**

`split_expr_1` is `lt(index, sload(array))` computed on the initcall'd state; recovering
the parameters turns it into the caller's own comparison.  This is the step that lets a
caller of the accessor know WHICH comparison decides the panic. -/
lemma index_flag_val_dyn {s₀ : State} {array index : Literal} (hok : isOk s₀) :
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
    initcall_evm_ai_dyn hok]

/-- The guard's flag, on the named guard state. -/
lemma arrIdxGuardStateDyn_flag {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardStateDyn array index s₀)["split_expr_1"]!!
      = (decide (index < Clear.EVMState.sload s₀.evm array)).toUInt256 := by
  unfold arrIdxGuardStateDyn
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  rw [lookup_insert' (by simpa [isOk_insert] using hf)]
  congr 1
  rw [lookup_insert_of_ne (by decide), lookup_insert' hf,
    Clear.lookup_initcall_snd hok (by decide), Clear.lookup_initcall_fst hok,
    initcall_evm_ai_dyn hok]

/-- The guard state keeps the caller's evm. -/
lemma arrIdxGuardStateDyn_evm {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardStateDyn array index s₀).evm = s₀.evm := by
  unfold arrIdxGuardStateDyn
  simp only [evm_insert]
  exact initcall_evm_ai_dyn hok

/-- The guard state still carries the caller's `array` argument. -/
lemma arrIdxGuardStateDyn_array {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardStateDyn array index s₀)["array"]!! = array := by
  unfold arrIdxGuardStateDyn
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  exact Clear.lookup_initcall_fst hok

/-- …and its `index` argument. -/
lemma arrIdxGuardStateDyn_index {array index : Literal} {s₀ : State} (hok : isOk s₀) :
    (arrIdxGuardStateDyn array index s₀)["index"]!! = index := by
  unfold arrIdxGuardStateDyn
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  exact Clear.lookup_initcall_snd hok (by decide)

/-- `arrIdxResultStateDyn` is out of fuel only if its input is. -/
lemma isOutOfFuel_arrIdxResultStateDyn {ss : State} : ❓ (arrIdxResultStateDyn ss) ↔ ❓ ss := by
  unfold arrIdxResultStateDyn
  simp only [isOutOfFuel_insert', isOutOfFuel_multifill', primCall_keccakOut,
    isOutOfFuel_setEvm']

/-- `arrIdxResultStateDyn` preserves `Ok`. -/
lemma isOk_arrIdxResultStateDyn {ss : State} (h : isOk ss) : isOk (arrIdxResultStateDyn ss) := by
  unfold arrIdxResultStateDyn
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
lemma storage_array_index_access_bytes32_dyn__dyn_val
    {slot offset : Identifier} {array index : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hso : slot ≠ offset)
    (hlt : index < Clear.EVMState.sload s₀.evm array)
    (h : A_storage_array_index_access_bytes32_dyn__dyn slot offset array index s₀ s₉) :
    s₉[slot]!! = (keccakOut ((s₀.evm).mstore 0 array) 0 32).1 + index := by
  obtain ⟨ss, hg, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "index"],[array, index]⟧) := isOk_initcall_of_isOk hok
  have hgcok : isOk (arrIdxGuardStateDyn array index s₀) := by
    unfold arrIdxGuardStateDyn; simpa [isOk_insert] using hf
  have hssnf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    rw [heq]
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_arrIdxResultStateDyn]
    exact hoo
  have hflag : (arrIdxGuardStateDyn array index s₀)["split_expr_1"]!! ≠ 0 := by
    rw [arrIdxGuardStateDyn_flag hok]; simp [hlt]
  have hss : ss = arrIdxGuardStateDyn array index s₀ :=
    (Spec_ok_unfold hgcok hssnf hg).1 hflag
  subst hss
  subst heq
  have hgcnf : ¬ ❓ (arrIdxGuardStateDyn array index s₀) := fun hoo =>
    isOk_and_isOutOfFuel ⟨hgcok, hoo⟩
  have hrev : isOk (🧟(arrIdxResultStateDyn (arrIdxGuardStateDyn array index s₀))) :=
    Clear.isOk_reviveJump_of_not_isOutOfFuel (by
      rw [isOutOfFuel_arrIdxResultStateDyn]; exact hgcnf)
  rw [lookup_insert' (isOk_insert.mpr (isOk_setStore_of_isOk hrev))]
  unfold arrIdxResultStateDyn
  set M := (arrIdxGuardStateDyn array index s₀)🇪⟦Clear.EVMState.mstore
    (arrIdxGuardStateDyn array index s₀).evm 0
    ((arrIdxGuardStateDyn array index s₀)["array"]!!)⟧ with hM
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
    Clear.lookup_setEvm hgcok, arrIdxGuardStateDyn_index hok,
    Clear.evm_setEvm_of_isOk hgcok, arrIdxGuardStateDyn_array hok, arrIdxGuardStateDyn_evm hok]


/-- **FRAME.**  The accessor writes only `slot` and `offset`; everything else is the
caller's.  Note this needs NO bounds hypothesis -- an out-of-range call reverts, and a
reverting call is not `Ok`, so `hnf` already covers it. -/
lemma storage_array_index_access_bytes32_dyn__dyn_frame
    {slot offset : Identifier} {array index : Literal} {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hvs : v ≠ slot) (hvo : v ≠ offset)
    (h : A_storage_array_index_access_bytes32_dyn__dyn slot offset array index s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  obtain ⟨ss, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 (arrIdxResultStateDyn ss)) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hvs, lookup_insert_of_ne hvo, Clear.lookup_setStore hrev hok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
