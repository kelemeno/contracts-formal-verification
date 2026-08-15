import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakDeterminism
import specs.KeccakDistinct
import specs.KeccakFuel
import specs.KeccakInjective
import specs.KeccakLowSlot
import specs.KeccakClean
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

/-- The value argument survives to the element write: nothing between the call and the
write rebinds `value0`, so what is stored is the caller's own argument. -/
lemma pushSt_value0 {array value0 : Literal} {s₀ : State} (hok : isOk s₀) :
    (pushSt s₀ array value0)["value0"]!! = value0 := by
  unfold pushSt
  rw [Clear.lookup_setEvm (isOk_pushInc hok)]
  unfold pushInc pushGc
  rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
    lookup_insert_of_ne (by decide)]
  exact Clear.lookup_initcall_snd hok (by decide)

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


/-- **A PUSH TOUCHES EXACTLY TWO SLOTS** -- the length, and the element at index `oldLen`.

Everything else in storage survives, which is what a caller needs in order to push onto one
level of the tree without disturbing another.  Together with `array_push_length` this pins
the push's whole storage effect: one slot incremented, one slot written, nothing else moved.

Note the accessor contributes NOTHING to this frame even on its panic branch: a bounds
failure is a flag in this model, not a rollback, and it writes no storage either way. -/
lemma array_push_sload_frame {array value0 : Literal} {q : UInt256} {s₀ s₉ : State}
    {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hnw : (Clear.EVMState.sload s₀.evm array).val + 1 < UInt256.size)
    (hqa : q ≠ array)
    (hqe : q ≠ (Clear.KeccakDeterminism.keccakOut ((Clear.EVMState.sstore s₀.evm array
          (Clear.EVMState.sload s₀.evm array + 1)).mstore 0 array) 0 32).1
        + Clear.EVMState.sload s₀.evm array)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
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
  have hlt : Clear.EVMState.sload s₀.evm array
      < Clear.EVMState.sload (pushSt s₀ array value0).evm array := by
    rw [pushSt_evm hok]
    exact Clear.StorageFrame.sload_lt_after_push hacc hnw
  have hslot : s₂["slot"]!!
      = (Clear.KeccakDeterminism.keccakOut
            (((pushSt s₀ array value0).evm).mstore 0 array) 0 32).1
        + Clear.EVMState.sload s₀.evm array :=
    storage_array_index_access_bytes32_dyn_ptr_val hstok h2nf (by decide) hlt ha₂
  rw [pushSt_evm (array := array) (value0 := value0) hok] at hslot
  have hq : q ≠ s₂["slot"]!! := by rw [hslot]; exact hqe
  have hs3ok : isOk s₃ := update_storage_value_bytes32_to_bytes32_isOk h3nf ha₃
  subst heq
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk hs3ok,
    update_storage_value_bytes32_to_bytes32_sload_frame hs2ok h3nf hq ha₃,
    storage_array_index_access_bytes32_dyn_ptr_sload hstok h2nf ha₂,
    pushSt_evm hok]
  exact Clear.KeccakDistinct.sload_sstore_of_ne s₀.evm hqa


/-- **THE ELEMENT YOU PUSHED IS THE ELEMENT THAT IS THERE.**

The value lands at the slot of index `oldLen` -- `keccak(array) + oldLen` over the evm the
element write sees -- and it is `value0`, the caller's argument, not something derived from
it.  With `array_push_length` (the length went up by one) and `array_push_sload_frame`
(nothing else moved) this completes the push: after it, `array[oldLen] = value0` and the
array is one longer.

`hnw` is the no-wrap side condition; `hacc` is the EVM well-formedness the storage model
needs for a write to read back, and the ACCOUNT FRAME is what carries it from `s₀` through
the length write and the address computation to the element write. -/
lemma array_push_val {array value0 : Literal} {s₀ s₉ : State} {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hnw : (Clear.EVMState.sload s₀.evm array).val + 1 < UInt256.size)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm
        ((Clear.KeccakDeterminism.keccakOut ((Clear.EVMState.sstore s₀.evm array
            (Clear.EVMState.sload s₀.evm array + 1)).mstore 0 array) 0 32).1
          + Clear.EVMState.sload s₀.evm array)
      = value0 := by
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
  have hs3ok : isOk s₃ := update_storage_value_bytes32_to_bytes32_isOk h3nf ha₃
  -- the account, carried from `s₀` through the length write and the accessor
  have hacc1 : Clear.EVMState.lookupAccount (pushSt s₀ array value0).evm
      (pushSt s₀ array value0).evm.execution_env.code_owner
        = some (act.updateStorage array (Clear.EVMState.sload s₀.evm array + 1)) := by
    rw [pushSt_evm hok]
    exact Clear.StorageFrame.lookupAccount_sstore_self hacc
  obtain ⟨haccS, henvS⟩ := storage_array_index_access_bytes32_dyn_ptr_account
    (addr := (pushSt s₀ array value0).evm.execution_env.code_owner) hstok h2nf ha₂
  have hacc2 : Clear.EVMState.lookupAccount s₂.evm s₂.evm.execution_env.code_owner
      = some (act.updateStorage array (Clear.EVMState.sload s₀.evm array + 1)) := by
    rw [henvS, haccS]; exact hacc1
  -- the write's arguments: word-aligned, and the value is the caller's
  have hoff : s₂["offset"]!! = 0 :=
    storage_array_index_access_bytes32_dyn_ptr_offset hstok h2nf (by decide) ha₂
  have hval : s₂["value0"]!! = value0 := by
    rw [storage_array_index_access_bytes32_dyn_ptr_frame hstok h2nf (by decide) (by decide) ha₂]
    exact pushSt_value0 hok
  -- and the slot, in closed form
  have hlt : Clear.EVMState.sload s₀.evm array
      < Clear.EVMState.sload (pushSt s₀ array value0).evm array := by
    rw [pushSt_evm hok]
    exact Clear.StorageFrame.sload_lt_after_push hacc hnw
  have hslot : s₂["slot"]!!
      = (Clear.KeccakDeterminism.keccakOut
            (((pushSt s₀ array value0).evm).mstore 0 array) 0 32).1
        + Clear.EVMState.sload s₀.evm array :=
    storage_array_index_access_bytes32_dyn_ptr_val hstok h2nf (by decide) hlt ha₂
  rw [pushSt_evm (array := array) (value0 := value0) hok] at hslot
  have hw := update_storage_value_bytes32_to_bytes32_val hs2ok h3nf hacc2 hoff ha₃
  rw [hslot, hval] at hw
  subst heq
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk hs3ok]
  exact hw

/-- The keccak window at the state the element write starts from.  The push's only step
before it is an `sstore`, which is neither `keccak_range` nor `keccak_map`. -/
lemma pushSt_config {array value0 : Literal} {s₀ : State} (hok : isOk s₀)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm) :
    Clear.KeccakLowSlot.RangeInWindow (pushSt s₀ array value0).evm ∧
      Clear.KeccakLowSlot.CachedInWindow (pushSt s₀ array value0).evm := by
  rw [pushSt_evm hok]
  exact ⟨Clear.StorageFrame.rangeInWindow_sstore hR,
    Clear.StorageFrame.cachedInWindow_sstore hC⟩

/-- Fuel at the same state.  The length write costs at most one unit, which is why a caller
has to budget for the WRITES on a path and not only for its hashes. -/
lemma pushSt_fuel {array value0 : Literal} {s₀ : State} {n : ℕ} (hok : isOk s₀)
    (hf : Clear.KeccakFuel.Fuel s₀.evm (n + 1)) :
    Clear.KeccakFuel.Fuel (pushSt s₀ array value0).evm n := by
  rw [pushSt_evm hok]
  exact Clear.KeccakFuel.Fuel.sstore _ _ hf

/-- **THE ELEMENT SLOT IS NOT THE LENGTH SLOT** -- derived, not assumed.

`array_push_length` takes this separation as a hypothesis, which is right for that lemma:
it keeps it free of the keccak configuration.  But a caller pushing onto a LITERAL slot can
discharge it outright, and this is how.  The element lives at `keccak(array) + oldLen`; the
window puts every hash above the low range and stops the index from wrapping back into it;
and `Fuel` is what says the hash drew a fresh slot at all rather than hitting the collision
fallback -- a fact about a state no caller can name, which is exactly why it has to arrive
as a propagated invariant. -/
lemma push_element_ne_low_slot {array value0 c : Literal} {s₀ : State} (hok : isOk s₀)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm array).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 2) :
    (Clear.KeccakDeterminism.keccakOut
        ((pushSt s₀ array value0).evm.mstore 0 array) 0 32).1
      + Clear.EVMState.sload s₀.evm array ≠ c := by
  obtain ⟨hRs, hCs⟩ := pushSt_config (array := array) (value0 := value0) hok hR hC
  have hRm := Clear.StorageFrame.rangeInWindow_mstore (a := 0) (v := array) hRs
  have hCm := Clear.StorageFrame.cachedInWindow_mstore (a := 0) (v := array) hCs
  have hfm : Clear.KeccakFuel.Fuel ((pushSt s₀ array value0).evm.mstore 0 array) 1 :=
    Clear.KeccakFuel.Fuel.mstore 0 array (pushSt_fuel (n := 1) hok hf)
  obtain ⟨r, σ', hsome⟩ := Clear.KeccakFuel.keccak256_some_of_fuel (p := 0) (q := 32) hfm
  have hko : Clear.KeccakDeterminism.keccakOut
      ((pushSt s₀ array value0).evm.mstore 0 array) 0 32 = (r, σ') := by
    unfold Clear.KeccakDeterminism.keccakOut
    rw [hsome]
  rw [hko]
  exact Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config _ _ hRm hCm hsome hidx hlow

/-- **PUSHING ONTO A LITERAL SLOT INCREMENTS ITS LENGTH** -- with no hypothesis about any
state the caller cannot name.

`array_push_length` takes the keccak separation as a hypothesis, deliberately, so that it
stays clear of the keccak configuration.  This is its corollary for the case the tree
actually uses: the array's slot is a compile-time constant, so it is a LOW slot, and the
separation follows from the window plus one unit of fuel.

Everything here is about `s₀`: the account exists, the length fits and does not wrap, the
slot and the current length are below `2 ^ 32`, the keccak window holds, and the pool has
two entries left -- one for the write and one for the hash.  That last one is the part worth
noticing: a caller has to budget fuel for the WRITES on a path, not only for its hashes. -/
lemma array_push_length_of_low_slot {array value0 : Literal} {s₀ s₉ : State} {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hnw : (Clear.EVMState.sload s₀.evm array).val + 1 < UInt256.size)
    (hlow : array.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm array).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 2)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm array = Clear.EVMState.sload s₀.evm array + 1 := by
  refine array_push_length hok hnf hacc hfits hnw ?_ h
  have hne := push_element_ne_low_slot (array := array) (value0 := value0) (c := array)
    hok hlow hidx hR hC hf
  rw [pushSt_evm hok] at hne
  exact fun hc => hne hc.symm

/-- **A PUSH ONTO A LITERAL SLOT LEAVES EVERY OTHER LOW SLOT ALONE** -- separations derived.

The companion to `array_push_length_of_low_slot`, and the form the tree needs: pushing onto
one level must not disturb the leaf count, the levels pointer or the defaults pointer, all of
which live at compile-time constant slots.  Both of the general frame's separation
hypotheses are discharged here -- `q ≠ array` is the caller's own business, and `q` misses
the ELEMENT slot because a low slot cannot be a keccak output offset by a small index. -/
lemma array_push_sload_frame_of_low_slot {array value0 : Literal} {q : Literal}
    {s₀ s₉ : State} {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hnw : (Clear.EVMState.sload s₀.evm array).val + 1 < UInt256.size)
    (hqa : q ≠ array)
    (hqlow : q.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm array).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hf : Clear.KeccakFuel.Fuel s₀.evm 2)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  refine array_push_sload_frame hok hnf hacc hfits hnw hqa ?_ h
  have hne := push_element_ne_low_slot (array := array) (value0 := value0) (c := q)
    hok hqlow hidx hR hC hf
  rw [pushSt_evm hok] at hne
  exact fun hc => hne hc.symm

/-- **THE PUSHED ELEMENT'S SLOT IS NEVER A LOW SLOT** -- paid for by the clean flag.

Same as `push_element_ne_low_slot` with the two units of pool replaced by the collision
flag on the state the hash produced.  Stated this way the result composes with everything
else on the tree paths, which all now trade in the flag: a caller that has to mix a budget
and a flag ends up owing both, and the budget half is the one it cannot always pay. -/
lemma push_element_ne_low_slot_of_clean {array value0 c : Literal} {s₀ : State}
    (hok : isOk s₀)
    (hlow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm array).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean (Clear.KeccakDeterminism.keccakOut
      ((pushSt s₀ array value0).evm.mstore 0 array) 0 32).2) :
    (Clear.KeccakDeterminism.keccakOut
        ((pushSt s₀ array value0).evm.mstore 0 array) 0 32).1
      + Clear.EVMState.sload s₀.evm array ≠ c := by
  obtain ⟨hRs, hCs⟩ := pushSt_config (array := array) (value0 := value0) hok hR hC
  have hRm := Clear.StorageFrame.rangeInWindow_mstore (a := 0) (v := array) hRs
  have hCm := Clear.StorageFrame.cachedInWindow_mstore (a := 0) (v := array) hCs
  -- the flag says the hash found the pool non-empty, which is all the budget ever bought
  have hsome := Clear.KeccakClean.keccak256_some_of_clean hclean
  exact Clear.KeccakLowSlot.keccak256_add_ne_lowSlot_of_config _ _ hRm hCm hsome hidx hlow

/-! ### Whole-call frames for the push

The internal `pushSt_*` lemmas describe the state just after the length write.  These carry
window and flag across the ENTIRE call, which is what a caller composing the push into a
larger block needs.  Both go through `array_push_normal`, which collapses the length-overflow
guard given `hfits` -- the guard's own frames would work too, but the normal form is shorter
and `hfits` is a hypothesis the caller has to supply for the length result anyway. -/

/-- **KECCAK WINDOW, WHOLE CALL.**  A length write, one address hash, one element write. -/
lemma array_push_config {array value0 : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨s₂, h₂, s₃, h₃, heq⟩ := array_push_normal hok hnf hfits h
  subst heq
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hstok h2nf h₂)
  obtain ⟨hRs, hCs⟩ := pushSt_config (array := array) (value0 := value0) hok hR hC
  obtain ⟨hR2, hC2⟩ := storage_array_index_access_bytes32_dyn_ptr_config hstok h2nf hRs hCs
    (Spec_ok_unfold hstok h2nf h₂)
  obtain ⟨hR3, hC3⟩ := update_storage_value_bytes32_to_bytes32_config hs2 h3nf hR2 hC2
    (Spec_ok_unfold hs2 h3nf h₃)
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk
    (update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃))]
  exact ⟨hR3, hC3⟩

/-- **CLEAN FLAG, BACKWARDS, WHOLE CALL.**  One hash, inside the address computation. -/
lemma array_push_clean {array value0 : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₂, h₂, s₃, h₃, heq⟩ := array_push_normal hok hnf hfits h
  subst heq
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hstok h2nf h₂)
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk
    (update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃))] at hclean
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    (update_storage_value_bytes32_to_bytes32_clean hs2 h3nf
      (Spec_ok_unfold hs2 h3nf h₃)).mp hclean
  have cst : Clear.KeccakClean.Clean (pushSt s₀ array value0).evm :=
    storage_array_index_access_bytes32_dyn_ptr_clean hstok h2nf c2
      (Spec_ok_unfold hstok h2nf h₂)
  rw [pushSt_evm hok, Clear.KeccakClean.clean_sstore] at cst
  exact cst

/-- **THE PUSH LEAVES EVERY OTHER LOW SLOT ALONE** -- paid for by the clean flag.

Cleaner than the budgeted `_of_low_slot`, and not only in its side conditions: that one
goes through `push_element_ne_low_slot`, which names the element slot in closed form and so
implicitly assumes the address computation took its non-panic branch.  This one asks the
ACCESSOR for the separation instead, and the accessor's `_slot_not_low_of_clean` holds on
BOTH branches of its bounds check -- so no case analysis is needed and no account witness
or non-wrap hypothesis is required.  What is left is exactly what matters: `c` is a literal
slot, it is not the length slot, and the length is not absurdly large. -/
lemma array_push_sload_frame_of_low_slot_of_clean {array value0 : Literal} {c : Literal}
    {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hqa : c ≠ array)
    (hqlow : c.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm array).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₂, h₂, s₃, h₃, heq⟩ := array_push_normal hok hnf hfits h
  subst heq
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hstok h2nf h₂)
  obtain ⟨hRs, hCs⟩ := pushSt_config (array := array) (value0 := value0) hok hR hC
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk
    (update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃))] at hclean ⊢
  -- the flag reaches the address computation, which is where the element slot is minted
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    (update_storage_value_bytes32_to_bytes32_clean hs2 h3nf
      (Spec_ok_unfold hs2 h3nf h₃)).mp hclean
  have hne : s₂["slot"]!! ≠ c :=
    storage_array_index_access_bytes32_dyn_ptr_slot_not_low_of_clean hstok h2nf hRs hCs c2
      hidx hqlow (Spec_ok_unfold hstok h2nf h₂)
  rw [update_storage_value_bytes32_to_bytes32_sload_frame hs2 h3nf (Ne.symm hne)
      (Spec_ok_unfold hs2 h3nf h₃),
    storage_array_index_access_bytes32_dyn_ptr_sload hstok h2nf (Spec_ok_unfold hstok h2nf h₂),
    pushSt_evm hok, Clear.KeccakDistinct.sload_sstore_of_ne _ hqa]

/-- **THE LENGTH GOES UP BY ONE** -- paid for by the clean flag.

Same shape as the frame above: the accessor supplies the separation on both branches, so
the only extra hypotheses over that lemma are the ones the WRITE needs -- an account to
store into, and the length not wrapping. -/
lemma array_push_length_of_low_slot_of_clean {array value0 : Literal} {s₀ s₉ : State}
    {act : Account}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hacc : Clear.EVMState.lookupAccount s₀.evm s₀.evm.execution_env.code_owner = some act)
    (hfits : Clear.EVMState.sload s₀.evm array < 18446744073709551616)
    (hlow : array.val < Clear.KeccakInjective.lowSlotBound)
    (hidx : (Clear.EVMState.sload s₀.evm array).val < Clear.KeccakInjective.lowSlotBound)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.EVMState.sload s₉.evm array = Clear.EVMState.sload s₀.evm array + 1 := by
  obtain ⟨s₂, h₂, s₃, h₃, heq⟩ := array_push_normal hok hnf hfits h
  subst heq
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have hstok : isOk (pushSt s₀ array value0) := isOk_pushSt hok
  have hs2 : isOk s₂ :=
    storage_array_index_access_bytes32_dyn_ptr_isOk h2nf (Spec_ok_unfold hstok h2nf h₂)
  obtain ⟨hRs, hCs⟩ := pushSt_config (array := array) (value0 := value0) hok hR hC
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk
    (update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃))] at hclean ⊢
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    (update_storage_value_bytes32_to_bytes32_clean hs2 h3nf
      (Spec_ok_unfold hs2 h3nf h₃)).mp hclean
  have hne : s₂["slot"]!! ≠ array :=
    storage_array_index_access_bytes32_dyn_ptr_slot_not_low_of_clean hstok h2nf hRs hCs c2
      hidx hlow (Spec_ok_unfold hstok h2nf h₂)
  rw [update_storage_value_bytes32_to_bytes32_sload_frame hs2 h3nf (Ne.symm hne)
      (Spec_ok_unfold hs2 h3nf h₃),
    storage_array_index_access_bytes32_dyn_ptr_sload hstok h2nf (Spec_ok_unfold hstok h2nf h₂),
    pushSt_evm hok, Clear.StorageFrame.sload_sstore_self hacc]

/-- **CLEAN FLAG, BACKWARDS, WITH NO SIDE CONDITION AT ALL.**

`array_push_clean` routes through `array_push_normal` and so inherits its `hfits`.  That is
avoidable: the length write, the address computation and the element write all run
UNCONDITIONALLY -- the guard decides whether to panic first, not whether the rest happens --
so the flag can be walked back through the guard itself, whose `_clean` is an iff.

The trick is to prove `isOk` and `.evm` of the guard's input tower INLINE rather than via
`isOk_pushGc`/`pushGc_evm`.  Those are stated about the simplified `pushGc`, which reads
`sload s₀.evm array` where the spec's tower reads `sload f.evm (f["array"]!!)` through the
initcall -- equal, but not defeq, and bridging them is the work `array_push_normal` exists
to do.  Elaborating the side goals against the tower itself sidesteps it entirely.

Worth having because a caller inside a loop may not know the array is small; the flag is
supposed to be the hypothesis that costs nothing, and this keeps that promise. -/
lemma array_push_clean_unconditional {array value0 : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := h
  have hgcok : isOk (s₀☎️⟦["array", "value0"],[array, value0]⟧) := isOk_initcall_of_isOk hok
  have h3nf : ¬ ❓ s₃ := by
    intro hoo; apply hnf; rw [heq]
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂
    (by simpa only [isOutOfFuel_setEvm', isOutOfFuel_insert'] using hoo))
  have a₁ := Spec_ok_unfold (by simp only [isOk_insert]; exact hgcok) h1nf h₁
  have hs1 : isOk s₁ := L2InteropCommitmentTree.Common.if_4590714779410500988_isOk
    (by simp only [isOk_insert]; exact hgcok) h1nf a₁
  have hincok : isOk (s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧) := isOk_insert.mpr hs1
  have hstok : isOk ((s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧)🇪⟦Clear.EVMState.sstore s₁.evm
      ((s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧)["array"]!!)
      ((s₁⟦"split_expr_1" ↦ s₁["oldLen"]!! + 1⟧)["split_expr_1"]!!)⟧) := by
    simp only [isOk_setEvm]; exact hincok
  have a₂ := Spec_ok_unfold hstok h2nf h₂
  have hs2 : isOk s₂ := storage_array_index_access_bytes32_dyn_ptr_isOk h2nf a₂
  rw [heq, evm_setStore, Clear.evm_reviveJump_of_isOk
    (update_storage_value_bytes32_to_bytes32_isOk h3nf (Spec_ok_unfold hs2 h3nf h₃))] at hclean
  have c2 : Clear.KeccakClean.Clean s₂.evm :=
    (update_storage_value_bytes32_to_bytes32_clean hs2 h3nf
      (Spec_ok_unfold hs2 h3nf h₃)).mp hclean
  have cst := storage_array_index_access_bytes32_dyn_ptr_clean hstok h2nf c2 a₂
  rw [Clear.evm_setEvm_of_isOk hincok, Clear.KeccakClean.clean_sstore] at cst
  have cgc := (L2InteropCommitmentTree.Common.if_4590714779410500988_clean
    (by simp only [isOk_insert]; exact hgcok) h1nf a₁).mp cst
  simpa only [evm_insert, Clear.evm_initcall hok] using cgc

/-- **FRAME.**  A push is a function call: it ends with a `setStore` back to the caller's
own varstore, so EVERY binding survives it -- there is no exception list. -/
lemma array_push_frame {array value0 : Literal} {v : Identifier} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_array_push_from_bytes32_to_array_bytes32_dyn_storage_ptr array value0 s₀ s₉) :
    s₉[v]!! = s₀[v]!! := by
  obtain ⟨s₁, _, s₂, _, s₃, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 s₃) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  exact Clear.lookup_setStore hrev hok

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
