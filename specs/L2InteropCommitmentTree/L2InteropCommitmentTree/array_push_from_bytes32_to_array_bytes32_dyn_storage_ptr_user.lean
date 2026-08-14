import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakDeterminism
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4590714779410500988
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x41
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Append to a dynamic storage array** — the deployed `push`.

```
    oldLen := sload(array)
    if iszero(lt(oldLen, 2^64)) { panic_error_0x41() }
    sstore(array, add(oldLen, 1))                       -- length := oldLen + 1
    slot, offset := storage_array_index_access(array, oldLen)
    update_storage_value_bytes32_to_bytes32(slot, offset, value0)
```

The shape gives the frame property the tree work needs: the length slot is set to
`oldLen + 1`, and the element write goes to the address of index `oldLen` — the
slot that was one PAST the end before this call.  No other slot is touched, and the
index written is not a caller argument but the length just read.

Note the ORDER: the length is incremented BEFORE the element is written, so the
bounds check inside `storage_array_index_access` (`index < sload(array)`) sees the
new length and admits `oldLen`.  Had the write come first, that check would reject
the very element being appended. -/
def A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr (array value0 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["array", "value0"],[array, value0]⟧
  let g := f⟦"oldLen" ↦ Clear.EVMState.sload f.evm (f["array"]!!)⟧
  let gc := g⟦"split_expr_0" ↦ (decide (g["oldLen"]!! < 18446744073709551616)).toUInt256⟧
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_if_4590714779410500988 gc s₁ ∧
    (let inc := s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧
     let st := inc🇪⟦Clear.EVMState.sstore s₁.evm (inc["array"]!!) (inc["split_expr_1"]!!)⟧
     ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "slot" "offset"
         (st["array"]!!) (st["oldLen"]!!)) st s₂ ∧
       ∃ s₃, Spec (A_update_storage_value_bytes32_to_bytes32
           (s₂["slot"]!!) (s₂["offset"]!!) (s₂["value0"]!!)) s₂ s₃ ∧
         s₉ = 🧟s₃🏪⟦s₀⟧)

lemma array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_abs_of_concrete {s₀ s₉ : State} {array value0} :
  Spec (array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_concrete_of_code.1 array value0) s₀ s₉ →
  Spec (A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0) s₀ s₉ := by
  unfold array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_concrete_of_code A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_not_break {array value0 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr_isOk hnf h)


/-- The callee state after `initcall` and the length read -- `Ok`, and its evm is the
caller's, which is what puts the push's hypotheses in closed form over `s₀`. -/
lemma array_push_pre_evm {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    ((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
      Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
        ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧).evm = s₀.evm := by
  simp only [evm_insert]
  exact Clear.evm_initcall hok

/-- The array argument, read back inside the callee. -/
lemma array_push_pre_array {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!! = array :=
  Clear.lookup_initcall_fst hok


/-- The push's overflow flag is set exactly when the length fits. -/
lemma array_push_flag {array value0 : Literal} {s₀ : State} (hok : isOk s₀)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616) :
    (((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
        Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
          ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧)⟦"split_expr_0" ↦
        (decide (((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
            Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
              ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧)["oldLen"]!!
          < 18446744073709551616)).toUInt256⟧)["split_expr_0"]!! ≠ 0 := by
  have hfok : isOk (s₀☎️⟦["array", "value0"],[array, value0]⟧) := isOk_initcall_of_isOk hok
  have hgok : isOk ((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
      Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
        ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧) := isOk_insert.mpr hfok
  -- the `.evm` occurrence here is the BARE initcall, not the "oldLen" state, so the
  -- frame lemma that applies is `evm_initcall` and not `array_push_pre_evm`
  rw [lookup_insert' hgok, lookup_insert' hfok, Clear.evm_initcall hok,
    array_push_pre_array (array := array) (value0 := value0) hok]
  simp [hfits]

/-! ### The push in closed form

Off the panic path every intermediate state of the push is a function of `s₀` alone: the
callee's evm is the caller's, and the array argument reads back as the literal passed in.
Naming those states is what lets the length and element lemmas be stated -- and proved --
without re-deriving the guard each time. -/

/-- The callee frame after the length read and the overflow guard. -/
def pushGc (s₀ : State) (array value0 : Literal) : State :=
  ((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
      Clear.EVMState.sload s₀.evm array⟧)⟦"split_expr_0" ↦
    (decide (Clear.EVMState.sload s₀.evm array < 18446744073709551616)).toUInt256⟧

/-- ... after the new length is computed, before it is stored. -/
def pushInc (s₀ : State) (array value0 : Literal) : State :=
  (pushGc s₀ array value0)⟦"split_expr_1" ↦ Clear.EVMState.sload s₀.evm array + 1⟧

/-- The state the element write starts from: the length slot ALREADY carries `oldLen + 1`,
because the deployed code stores the length before computing the element's address. -/
def pushSt (s₀ : State) (array value0 : Literal) : State :=
  (pushInc s₀ array value0)🇪⟦Clear.EVMState.sstore s₀.evm array
    (Clear.EVMState.sload s₀.evm array + 1)⟧

lemma isOk_pushGc {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (pushGc s₀ array value0) :=
  isOk_insert.mpr (isOk_insert.mpr (isOk_initcall_of_isOk hok))

lemma isOk_pushInc {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (pushInc s₀ array value0) :=
  isOk_insert.mpr (isOk_pushGc hok)

lemma isOk_pushSt {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    isOk (pushSt s₀ array value0) := by
  unfold pushSt
  rw [isOk_setEvm]
  exact isOk_pushInc hok

lemma pushGc_evm {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushGc s₀ array value0).evm = s₀.evm := by
  unfold pushGc
  simp only [evm_insert]
  exact Clear.evm_initcall hok

lemma pushGc_oldLen {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushGc s₀ array value0)["oldLen"]!! = Clear.EVMState.sload s₀.evm array := by
  unfold pushGc
  rw [lookup_insert_of_ne (by decide)]
  exact lookup_insert' (isOk_initcall_of_isOk hok)

/-- The guard flag, in closed form: nonzero exactly when the length fits. -/
lemma pushGc_flag {array value0 : Literal} {s₀ : State} (hok : isOk s₀)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616) :
    (pushGc s₀ array value0)["split_expr_0"]!! ≠ 0 := by
  unfold pushGc
  rw [lookup_insert' (isOk_insert.mpr (isOk_initcall_of_isOk hok))]
  simp [hfits]

lemma pushInc_array {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushInc s₀ array value0)["array"]!! = array := by
  unfold pushInc pushGc
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
    lookup_insert_of_ne (by decide)]
  exact Clear.lookup_initcall_fst hok

lemma pushInc_split1 {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushInc s₀ array value0)["split_expr_1"]!! = Clear.EVMState.sload s₀.evm array + 1 := by
  unfold pushInc
  exact lookup_insert' (isOk_pushGc hok)

lemma pushSt_array {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushSt s₀ array value0)["array"]!! = array := by
  unfold pushSt
  rw [Clear.lookup_setEvm (isOk_pushInc hok)]
  exact pushInc_array hok

lemma pushSt_oldLen {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushSt s₀ array value0)["oldLen"]!! = Clear.EVMState.sload s₀.evm array := by
  unfold pushSt
  rw [Clear.lookup_setEvm (isOk_pushInc hok)]
  unfold pushInc
  rw [lookup_insert_of_ne (by decide)]
  exact pushGc_oldLen hok

/-- **THE LENGTH IS ALREADY INCREMENTED** when the element's address is computed. -/
lemma pushSt_evm {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushSt s₀ array value0).evm
      = Clear.EVMState.sstore s₀.evm array (Clear.EVMState.sload s₀.evm array + 1) := by
  unfold pushSt
  exact Clear.evm_setEvm_of_isOk (isOk_pushInc hok)


/-- **THE PUSH IN NORMAL FORM.**  Off the panic path the guard vanishes and the two
remaining calls -- the index accessor and the element write -- both start from `pushSt`,
which is closed over `s₀`.  Everything a caller wants to know about a push (the length
went up by one, the element landed at index `oldLen`, nothing else moved) is a statement
about this shape, so it is worth extracting once. -/
lemma array_push_normal {array value0 : Literal} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    ∃ s₂, Spec (A_storage_array_index_access_bytes32_dyn_ptr "slot" "offset"
        array (Clear.EVMState.sload s₀.evm array)) (pushSt s₀ array value0) s₂ ∧
      ∃ s₃, Spec (A_update_storage_value_bytes32_to_bytes32
          (s₂["slot"]!!) (s₂["offset"]!!) (s₂["value0"]!!)) s₂ s₃ ∧
        s₉ = 🧟s₃🏪⟦s₀⟧ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  have hf : isOk (s₀☎️⟦["array", "value0"],[array, value0]⟧) := isOk_initcall_of_isOk hok
  -- the spec writes the guard state over the CALLEE's evm; under `hok` that is `s₀`'s
  have hgceq : ((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
        Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
          ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧)⟦"split_expr_0" ↦
      (decide (((s₀☎️⟦["array", "value0"],[array, value0]⟧)⟦"oldLen" ↦
          Clear.EVMState.sload (s₀☎️⟦["array", "value0"],[array, value0]⟧).evm
            ((s₀☎️⟦["array", "value0"],[array, value0]⟧)["array"]!!)⟧)["oldLen"]!!
        < 18446744073709551616)).toUInt256⟧ = pushGc s₀ array value0 := by
    rw [Clear.evm_initcall hok, Clear.lookup_initcall_fst hok, lookup_insert' hf]
    rfl
  rw [hgceq] at h₁
  -- fuel travels backwards along the call chain
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := by
    intro hoo
    apply h2nf
    apply Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    simpa only [isOutOfFuel_setEvm', isOutOfFuel_insert'] using hoo
  have hs1 : s₁ = pushGc s₀ array value0 :=
    L2InteropCommitmentTree.Common.if_4590714779410500988_id_of_ne (pushGc_flag hok hfits)
      (Spec_ok_unfold (isOk_pushGc hok) h1nf h₁)
  subst hs1
  have hsteq : ((pushGc s₀ array value0)⟦"split_expr_1" ↦
        (pushGc s₀ array value0)["oldLen"]!! + 1⟧)🇪⟦
      Clear.EVMState.sstore (pushGc s₀ array value0).evm
        (((pushGc s₀ array value0)⟦"split_expr_1" ↦
          (pushGc s₀ array value0)["oldLen"]!! + 1⟧)["array"]!!)
        (((pushGc s₀ array value0)⟦"split_expr_1" ↦
          (pushGc s₀ array value0)["oldLen"]!! + 1⟧)["split_expr_1"]!!)⟧
      = pushSt s₀ array value0 := by
    rw [pushGc_oldLen hok, pushGc_evm hok]
    show ((pushInc s₀ array value0)🇪⟦Clear.EVMState.sstore s₀.evm
      ((pushInc s₀ array value0)["array"]!!)
      ((pushInc s₀ array value0)["split_expr_1"]!!)⟧) = _
    rw [pushInc_array hok, pushInc_split1 hok]
    rfl
  rw [hsteq, pushSt_array hok, pushSt_oldLen hok] at h₂
  exact ⟨s₂, h₂, s₃, h₃, heq⟩


/-- **THE PUSH INCREMENTS THE LENGTH -- AND ONLY BY ONE.**

The tree's `nodes[level]` arrays grow one leaf at a time, and the fold's step count is
pinned to those lengths, so "a push adds exactly one" is the fact that keeps a level's
length in step with the number of insertions.  Anything weaker (the length merely grew)
would let a level run ahead of its siblings.

Three side conditions, all real and all the caller's:
  * `hfits`  the array is shorter than `2 ^ 64`, so the guard does not panic;
  * `hnw`    the increment does not wrap the word -- implied by `hfits` in any real tree,
             but a separate arithmetic fact and stated as one;
  * `hsep`   the element's slot is not the length slot.  In closed form this is
             `array ≠ keccak(array) + oldLen`, which the keccak low-slot separation
             discharges for a literal `array`; taking it as a hypothesis keeps this lemma
             free of the keccak configuration.

`hacc` is the EVM well-formedness the storage model needs for a write to read back. -/
lemma array_push_length {array value0 : Literal} {s₀ s₉ : State} {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hnw : (Clear.EVMState.sload s₀.evm array).val + 1 < UInt256.size)
    (hsep : array ≠ (Clear.KeccakDeterminism.keccakOut ((Clear.EVMState.sstore s₀.evm array
          (Clear.EVMState.sload s₀.evm array + 1)).mstore 0 array) 0 32).1
        + Clear.EVMState.sload s₀.evm array)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm array = Clear.EVMState.sload s₀.evm array + 1 := by
  obtain ⟨s₂, h₂, s₃, h₃, heq⟩ := array_push_normal hok hnf hfits h
  have h3nf : ¬ ❓ s₃ := by
    intro hoo
    apply hnf
    rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have ha₂ := Spec_ok_unfold hstok h2nf h₂
  have hs2ok : isOk s₂ := storage_array_index_access_bytes32_dyn_ptr_isOk h2nf ha₂
  have ha₃ := Spec_ok_unfold hs2ok h3nf h₃
  -- the bounds check sees the NEW length, which is why index `oldLen` is admitted
  have hlt : Clear.EVMState.sload s₀.evm array
      < Clear.EVMState.sload (pushSt s₀ array value0).evm array := by
    rw [pushSt_evm hok]
    exact Clear.StorageFrame.sload_lt_after_push hacc hnw
  have hslot : s₂["slot"]!!
      = (Clear.KeccakDeterminism.keccakOut (((pushSt s₀ array value0).evm).mstore 0 array) 0 32).1
        + Clear.EVMState.sload s₀.evm array :=
    storage_array_index_access_bytes32_dyn_ptr_val hstok h2nf (by decide) hlt ha₂
  rw [pushSt_evm (array := array) (value0 := value0) hok] at hslot
  have hq : array ≠ s₂["slot"]!! := by rw [hslot]; exact hsep
  have hs3ok : isOk s₃ := update_storage_value_bytes32_to_bytes32_isOk h3nf ha₃
  -- walk the length slot back: element write misses it, accessor writes nothing,
  -- and the `sstore` reads back
  subst heq
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk hs3ok,
    update_storage_value_bytes32_to_bytes32_sload_frame hs2ok h3nf hq ha₃,
    storage_array_index_access_bytes32_dyn_ptr_sload hstok h2nf ha₂,
    pushSt_evm hok]
  exact Clear.StorageFrame.sload_sstore_self hacc


end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
